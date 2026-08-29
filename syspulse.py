"""SysPulse Ultra v9.1: a terminal monitor with cached Linux diagnostics.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import re
import shutil
import signal
import socket
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from typing import Any, Dict, List, Optional, Tuple

try:
    import psutil
except ImportError:
    print("psutil is required. Install with: pip install psutil", file=sys.stderr)
    raise

try:
    from tabulate import tabulate
except ImportError:
    tabulate = None  # fallback to simple printing later

try:
    from colorama import Fore, Style, init as colorama_init
except Exception:
    # Provide minimal fallbacks if colorama isn't available
    class _F:
        RED = YELLOW = GREEN = CYAN = WHITE = RESET = ""
    Fore = Style = _F()
    def colorama_init(*_, **__): pass

colorama_init(autoreset=True)


class _NoColor:
    RED = YELLOW = GREEN = CYAN = WHITE = RESET = BRIGHT = ""


def disable_color_output() -> None:
    """Make the existing dashboard formatter safe for plain-text logs and pipes."""
    global Fore, Style
    Fore = _NoColor()
    Style = _NoColor()


# Config / thresholds
CPU_WARN, CPU_CRIT = 85, 95
RAM_WARN, RAM_CRIT = 80, 90
DISK_WARN, DISK_CRIT = 85, 95
TEMP_WARN, TEMP_CRIT = 80, 90
LAT_WARN, LAT_CRIT = 100, 200

DEFAULT_REFRESH = 1.5
DEFAULT_MAX_HISTORY = 1000
PING_HOST_DEFAULT = "1.1.1.1"
DEFAULT_DIAGNOSTIC_INTERVAL = 300.0
DEFAULT_CONTAINER_INTERVAL = 30.0


# Helpers
def size(n: Optional[float]) -> str:
    if n is None:
        return "N/A"
    try:
        n = float(n)
    except (TypeError, ValueError):
        return "N/A"
    for unit in ("B", "KB", "MB", "GB", "TB", "PB"):
        if abs(n) < 1024:
            return f"{n:,.2f} {unit}"
        n /= 1024
    return f"{n:,.2f} EB"


def bar(value: float, width: int = 20) -> str:
    if value is None:
        value = 0.0
    value = max(0.0, min(100.0, float(value)))
    filled = int(value / 100.0 * width)
    return "█" * filled + "░" * (width - filled)


def col(value: Optional[float], warning: float, critical: float) -> str:
    try:
        v = float(value)
    except Exception:
        return Fore.GREEN
    if v >= critical:
        return Fore.RED
    if v >= warning:
        return Fore.YELLOW
    return Fore.GREEN


def uptime(seconds: float) -> str:
    seconds = int(seconds)
    days, rem = divmod(seconds, 86400)
    hours, rem = divmod(rem, 3600)
    minutes, seconds = divmod(rem, 60)
    if days:
        return f"{days}d {hours}h {minutes}m"
    if hours:
        return f"{hours}h {minutes}m {seconds}s"
    return f"{minutes}m {seconds}s"


def safe_read_int(path: str) -> Optional[int]:
    try:
        with open(path, "r", encoding="utf-8") as f:
            return int(f.read().strip())
    except Exception:
        return None


# Probes (mostly original logic, but cleaned)

def battery_health() -> Optional[Dict[str, Any]]:
    """Read battery design/full capacity from Linux sysfs.

    Supports both energy-based (mWh) and charge-based (mAh) batteries.
    Returns None when no BAT* device or usable capacity information exists.
    """
    power_supply = "/sys/class/power_supply"

    if not os.path.isdir(power_supply):
        return None

    try:
        batteries = [
            os.path.join(power_supply, name)
            for name in os.listdir(power_supply)
            if name.startswith("BAT")
        ]
    except OSError:
        return None

    if not batteries:
        return None

    root = batteries[0]

    for design, full, unit in (
        ("energy_full_design", "energy_full", "mWh"),
        ("charge_full_design", "charge_full", "mAh"),
    ):
        design_path = os.path.join(root, design)
        full_path = os.path.join(root, full)

        if os.path.exists(design_path) and os.path.exists(full_path):
            design_value = safe_read_int(design_path)
            full_value = safe_read_int(full_path)

            if design_value and full_value and design_value > 0:
                return {
                    "health": max(0.0, min(100.0, full_value / design_value * 100.0)),
                    "design": design_value / 1000.0,
                    "full": full_value / 1000.0,
                    "unit": unit,
                }

    return None


def battery_info() -> Optional[Dict[str, Any]]:
    """Get battery information using psutil, with a Linux sysfs fallback.

    Some Linux laptops expose the battery through /sys/class/power_supply/
    even when psutil.sensors_battery() returns None. This fallback prevents
    the dashboard from incorrectly showing N/A on those systems.
    """

    # First try psutil.
    try:
        b = psutil.sensors_battery()
        if b is not None:
            result: Dict[str, Any] = {
                "percent": float(b.percent) if b.percent is not None else 0.0,
                "charging": bool(b.power_plugged),
                "seconds_left": b.secsleft,
            }

            health = battery_health()
            if health:
                result.update(health)

            return result
    except Exception:
        pass

    # Linux fallback: read the kernel power-supply interface directly.
    power_supply = "/sys/class/power_supply"
    if not os.path.isdir(power_supply):
        return None

    try:
        batteries = [
            name for name in os.listdir(power_supply)
            if name.startswith("BAT")
        ]
    except OSError:
        return None

    if not batteries:
        return None

    root = os.path.join(power_supply, batteries[0])

    capacity = safe_read_int(os.path.join(root, "capacity"))
    status = read_text(os.path.join(root, "status"))

    # Clamp bad/driver-reported values so the dashboard remains sane.
    percent = float(capacity) if capacity is not None else 0.0
    percent = max(0.0, min(100.0, percent))

    charging = None
    if status:
        status_lower = status.strip().lower()
        if status_lower in {"charging", "full"}:
            charging = True
        elif status_lower in {"discharging", "not charging", "unknown"}:
            charging = False

    # Estimate remaining time from energy or charge/current values.
    seconds_left: Optional[float] = None

    try:
        energy_now = safe_read_int(os.path.join(root, "energy_now"))
        power_now = safe_read_int(os.path.join(root, "power_now"))

        if energy_now is not None and power_now is not None and power_now > 0:
            # Both values are normally exposed in microwatt-hours /
            # microwatts, so their ratio is hours.
            seconds_left = max(0.0, (energy_now / power_now) * 3600.0)
    except Exception:
        pass

    if seconds_left is None:
        try:
            charge_now = safe_read_int(os.path.join(root, "charge_now"))
            current_now = safe_read_int(os.path.join(root, "current_now"))

            if charge_now is not None and current_now is not None and current_now > 0:
                seconds_left = max(0.0, (charge_now / current_now) * 3600.0)
        except Exception:
            pass

    result = {
        "percent": percent,
        "charging": bool(charging) if charging is not None else False,
        "seconds_left": seconds_left,
    }

    health = battery_health()
    if health:
        result.update(health)

    return result


def sensors() -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
    temps = []
    fans = []
    try:
        data = psutil.sensors_temperatures()
        for group, items in data.items():
            for x in items:
                if x.current is not None:
                    temps.append({
                        "name": x.label or group,
                        "temp": x.current,
                        "high": x.high,
                        "critical": x.critical
                    })
    except Exception:
        pass
    try:
        data = psutil.sensors_fans()
        for group, items in data.items():
            for x in items:
                if x.current is not None:
                    fans.append({
                        "name": x.label or group,
                        "rpm": x.current
                    })
    except Exception:
        pass
    return temps, fans


def storage() -> List[Dict[str, Any]]:
    result: List[Dict[str, Any]] = []
    seen_mounts = set()
    for part in psutil.disk_partitions(all=False):
        if part.fstype in {
            "tmpfs", "devtmpfs", "squashfs",
            "overlay", "proc", "sysfs",
            "cgroup", "cgroup2"
        }:
            continue
        if part.mountpoint in seen_mounts:
            continue
        try:
            u = psutil.disk_usage(part.mountpoint)
            result.append({
                "device": part.device,
                "mount": part.mountpoint,
                "type": part.fstype,
                "total": u.total,
                "used": u.used,
                "free": u.free,
                "percent": u.percent
            })
            seen_mounts.add(part.mountpoint)
        except (OSError, PermissionError):
            continue
    return result


def nvidia_gpu() -> List[Dict[str, Any]]:
    smi = shutil.which("nvidia-smi")
    if not smi:
        return []
    query = (
        "name,temperature.gpu,utilization.gpu,"
        "memory.used,memory.total,power.draw"
    )
    try:
        output = subprocess.check_output(
            [smi, f"--query-gpu={query}", "--format=csv,noheader,nounits"],
            text=True,
            timeout=2
        )
        result = []
        for line in output.strip().splitlines():
            v = [x.strip() for x in line.split(",")]
            if len(v) != 6:
                continue
            try:
                result.append({
                    "name": v[0],
                    "temp": float(v[1]),
                    "usage": float(v[2]),
                    "vram_used": float(v[3]),
                    "vram_total": float(v[4]),
                    "power": float(v[5])
                })
            except ValueError:
                continue
        return result
    except Exception:
        return []


def logged_users() -> List[Dict[str, Any]]:
    try:
        return [{"name": u.name, "terminal": u.terminal, "host": u.host} for u in psutil.users()]
    except Exception:
        return []


def failed_services() -> Optional[List[str]]:
    systemctl = shutil.which("systemctl")
    if not systemctl:
        return None
    try:
        result = subprocess.run(
            [systemctl, "--failed", "--no-legend", "--plain"],
            capture_output=True,
            text=True,
            timeout=3
        )
        if result.returncode not in (0, 1):
            return None
        lines = [x.strip() for x in result.stdout.splitlines() if x.strip()]
        return lines
    except Exception:
        return None


# Stateful rate calculators
class RateTracker:
    def __init__(self):
        self.prev = None

    def update(self, current, now: float, read_attr: str, write_attr: str) -> Dict[str, float]:
        rates = {"read": 0.0, "write": 0.0}
        if self.prev:
            old, old_time = self.prev
            dt = now - old_time
            if dt > 0:
                try:
                    read_now = getattr(current, read_attr)
                    write_now = getattr(current, write_attr)
                    read_old = getattr(old, read_attr)
                    write_old = getattr(old, write_attr)
                    rates["read"] = max(0.0, read_now - read_old) / dt
                    rates["write"] = max(0.0, write_now - write_old) / dt
                except Exception:
                    pass
        self.prev = (current, now)
        return rates


# Process stats
def process_stats(limit: int = 5) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]], int, int]:
    # Ensure cpu_percent has been primed by caller
    result = []
    for p in psutil.process_iter(["pid", "name", "cpu_percent", "memory_percent", "status"]):
        try:
            i = p.info
            result.append({
                "pid": i.get("pid"),
                "name": i.get("name") or "Unknown",
                "cpu": i.get("cpu_percent") or 0.0,
                "ram": i.get("memory_percent") or 0.0,
                "status": i.get("status")
            })
        except (psutil.NoSuchProcess, psutil.AccessDenied):
            continue
    top_cpu = sorted(result, key=lambda x: x["cpu"], reverse=True)[:limit]
    top_ram = sorted(result, key=lambda x: x["ram"], reverse=True)[:limit]
    zombies = sum(1 for x in result if x.get("status") == psutil.STATUS_ZOMBIE)
    return top_cpu, top_ram, len(result), zombies


# Network helpers
def network_rates(prev_net: Optional[Dict[str, Any]], now_time: float) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    current = psutil.net_io_counters(pernic=True)
    rates = {}
    if prev_net:
        old, old_time = prev_net
        dt = now_time - old_time
        if dt > 0:
            for name, value in current.items():
                if name not in old:
                    continue
                rates[name] = {
                    "down": max(0.0, value.bytes_recv - old[name].bytes_recv) / dt,
                    "up": max(0.0, value.bytes_sent - old[name].bytes_sent) / dt,
                    "rx": value.packets_recv,
                    "tx": value.packets_sent,
                    "rx_err": value.errin,
                    "tx_err": value.errout,
                    "rx_drop": value.dropin,
                    "tx_drop": value.dropout
                }
    return current, rates


def ipv4_addresses() -> Dict[str, str]:
    result = {}
    try:
        interfaces = psutil.net_if_addrs()
    except (psutil.AccessDenied, PermissionError, OSError):
        return result
    for interface, addresses in interfaces.items():
        for address in addresses:
            if address.family == socket.AF_INET:
                result[interface] = address.address
                break
    return result


# Latency (ping)
def latency(host: str = PING_HOST_DEFAULT) -> Optional[float]:
    ping = shutil.which("ping")
    if not ping:
        return None
    if sys.platform.startswith("win"):
        cmd = [ping, "-n", "1", "-w", "1000", host]
    else:
        cmd = [ping, "-c", "1", "-W", "1", host]
    try:
        start = time.perf_counter()
        r = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=2)
        if r.returncode == 0:
            return (time.perf_counter() - start) * 1000.0
    except Exception:
        pass
    return None


# Extended diagnostics (features 12–20)
def command_text(command: List[str], timeout: float = 5.0) -> Tuple[int, str, str]:
    """Run a read-only diagnostic command without raising on absent tools."""
    try:
        result = subprocess.run(
            command,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return result.returncode, result.stdout.strip(), result.stderr.strip()
    except (OSError, subprocess.SubprocessError):
        return 127, "", ""


def read_text(path: str) -> Optional[str]:
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as file:
            return file.read().strip()
    except OSError:
        return None


def physical_block_devices(limit: int = 4) -> List[str]:
    """Return up to ``limit`` whole block devices, excluding partitions and RAM disks."""
    root = "/sys/class/block"
    excluded = ("loop", "ram", "dm-", "sr", "fd", "zram", "md")
    devices: List[str] = []
    try:
        names = sorted(os.listdir(root))
    except OSError:
        return devices
    for name in names:
        if name.startswith(excluded):
            continue
        if os.path.exists(os.path.join(root, name, "partition")):
            continue
        device = f"/dev/{name}"
        if os.path.exists(device):
            devices.append(device)
        if len(devices) >= limit:
            break
    return devices


def disk_health() -> List[Dict[str, Any]]:
    """Collect best-effort NVMe/SMART health without sudo or write operations."""
    smartctl = shutil.which("smartctl")
    nvme = shutil.which("nvme")
    results: List[Dict[str, Any]] = []

    for device in physical_block_devices(limit=2):
        base = os.path.basename(device)
        item: Dict[str, Any] = {
            "device": device,
            "model": read_text(f"/sys/class/block/{base}/device/model") or "Unknown",
            "type": "NVMe" if base.startswith("nvme") else "SMART",
            "health": "UNAVAILABLE",
            "temperature": None,
            "wear": None,
            "power_on_hours": None,
            "media_errors": None,
            "checked": False,
        }
        if base.startswith("nvme") and nvme:
            code, output, _ = command_text([nvme, "smart-log", device], timeout=5)
            if code == 0 and output:
                item["checked"] = True
                critical = re.search(r"critical_warning\s*:\s*(?:0x)?([0-9a-f]+)", output, re.I)
                item["health"] = "PASSED" if critical and int(critical.group(1), 16) == 0 else "CHECK"
                for key, pattern, cast in (
                    ("temperature", r"temperature\s*:\s*(\d+)", float),
                    ("wear", r"percentage_used\s*:\s*(\d+)", float),
                    ("power_on_hours", r"power_on_hours\s*:\s*(\d+)", int),
                    ("media_errors", r"media_errors\s*:\s*(\d+)", int),
                ):
                    match = re.search(pattern, output, re.I)
                    if match:
                        item[key] = cast(match.group(1))
            results.append(item)
            continue

        if smartctl:
            code, output, error = command_text([smartctl, "-H", "-A", device], timeout=5)
            combined = f"{output}\n{error}"
            if code == 0 and output:
                item["checked"] = True
                if re.search(r"(?:overall-health|health status).*?(?:PASSED|OK)", output, re.I):
                    item["health"] = "PASSED"
                elif re.search(r"(?:overall-health|health status)", output, re.I):
                    item["health"] = "CHECK"
                for key, pattern, cast in (
                    ("temperature", r"(?:Temperature_Celsius|Airflow_Temperature_Cel).*?(\d+)\s*$", float),
                    ("power_on_hours", r"Power_On_Hours.*?(\d+)\s*$", int),
                    ("media_errors", r"(?:Reallocated_Sector_Ct|Reported_Uncorrect).*?(\d+)\s*$", int),
                ):
                    match = re.search(pattern, output, re.I | re.M)
                    if match:
                        item[key] = cast(match.group(1))
            elif combined and "permission" not in combined.lower():
                item["health"] = "CHECK"
        results.append(item)
    return results


def boot_health() -> Dict[str, Any]:
    """Collect startup duration and the slowest systemd services when available."""
    result: Dict[str, Any] = {
        "available": False,
        "boot_time": None,
        "kernel_time": None,
        "userspace_time": None,
        "slow_services": [],
    }
    analyze = shutil.which("systemd-analyze")
    if not analyze:
        return result
    code, output, _ = command_text([analyze], timeout=5)
    if code == 0:
        result["available"] = True
        total = re.search(r"=\s*([0-9.]+)s", output)
        kernel = re.search(r"([0-9.]+)s\s*\(kernel\)", output)
        userspace = re.search(r"([0-9.]+)s\s*\(userspace\)", output)
        if total:
            result["boot_time"] = float(total.group(1))
        if kernel:
            result["kernel_time"] = float(kernel.group(1))
        if userspace:
            result["userspace_time"] = float(userspace.group(1))
    code, output, _ = command_text([analyze, "blame"], timeout=6)
    if code == 0:
        result["available"] = True
        result["slow_services"] = [line.strip() for line in output.splitlines()[:8] if line.strip()]
    return result


def security_health() -> Dict[str, Any]:
    """Summarise local exposure without changing firewall or service state."""
    result: Dict[str, Any] = {
        "firewall": "UNKNOWN",
        "listening_ports": None,
        "ssh": "UNKNOWN",
        "failed_auth": None,
        "root_processes": None,
    }
    ufw = shutil.which("ufw")
    firewall_cmd = shutil.which("firewall-cmd")
    if ufw:
        code, output, _ = command_text([ufw, "status"], timeout=4)
        if code == 0:
            result["firewall"] = "ACTIVE" if re.search(r"Status:\s*active", output, re.I) else "INACTIVE"
    elif firewall_cmd:
        code, output, _ = command_text([firewall_cmd, "--state"], timeout=4)
        if code == 0:
            result["firewall"] = "ACTIVE" if output.strip().lower() == "running" else "INACTIVE"

    try:
        result["listening_ports"] = sum(
            connection.status == psutil.CONN_LISTEN
            for connection in psutil.net_connections(kind="inet")
        )
    except (psutil.AccessDenied, PermissionError, OSError):
        pass

    systemctl = shutil.which("systemctl")
    if systemctl:
        for service in ("ssh", "sshd"):
            code, output, _ = command_text([systemctl, "is-active", service], timeout=3)
            if code == 0 and output.strip() == "active":
                result["ssh"] = "ACTIVE"
                break
        else:
            result["ssh"] = "NOT ACTIVE"

    journalctl = shutil.which("journalctl")
    if journalctl:
        code, output, _ = command_text([journalctl, "-b", "--no-pager", "-n", "1000"], timeout=8)
        if code == 0:
            result["failed_auth"] = sum(
                any(term in line.lower() for term in ("failed password", "authentication failure", "invalid user"))
                for line in output.splitlines()
            )
    try:
        result["root_processes"] = sum(
            process.info.get("username") == "root"
            for process in psutil.process_iter(["username"])
        )
    except (psutil.AccessDenied, psutil.NoSuchProcess):
        pass
    return result


def kernel_health() -> Dict[str, Any]:
    """Report kernel taint, loaded modules, and current-boot kernel events."""
    taint = read_text("/proc/sys/kernel/tainted")
    modules_text = read_text("/proc/modules")
    result: Dict[str, Any] = {
        "version": platform.release(),
        "taint": taint if taint is not None else "UNKNOWN",
        "tainted": taint not in (None, "0"),
        "modules": len(modules_text.splitlines()) if modules_text else None,
        "oom": 0,
        "errors": 0,
        "warnings": 0,
        "available": False,
    }
    journalctl = shutil.which("journalctl")
    if journalctl:
        code, output, _ = command_text([journalctl, "-k", "-b", "--no-pager", "-n", "1000"], timeout=8)
        if code == 0:
            result["available"] = True
            lines = [line.lower() for line in output.splitlines()]
            result["oom"] = sum("out of memory" in line or "oom-kill" in line for line in lines)
            result["errors"] = sum(any(word in line for word in ("error", "failed", "failure")) for line in lines)
            result["warnings"] = sum("warning" in line or "warn" in line for line in lines)
    return result


def log_analyzer(lines_limit: int = 600) -> Dict[str, Any]:
    """Summarise errors and retain a short, readable current-boot log sample."""
    result: Dict[str, Any] = {"available": False, "critical": 0, "errors": 0, "warnings": 0, "recent": []}
    journalctl = shutil.which("journalctl")
    if not journalctl:
        return result
    code, output, _ = command_text(
        [journalctl, "-b", "--no-pager", "-n", str(lines_limit), "-o", "short"], timeout=8
    )
    if code != 0:
        return result
    result["available"] = True
    noteworthy: List[str] = []
    for line in output.splitlines():
        low = line.lower()
        if "critical" in low:
            result["critical"] += 1
            noteworthy.append(line)
        elif "error" in low or "failed" in low:
            result["errors"] += 1
            noteworthy.append(line)
        elif "warning" in low or "warn" in low:
            result["warnings"] += 1
            noteworthy.append(line)
    result["recent"] = noteworthy[-6:]
    return result


def package_health() -> Dict[str, Any]:
    """Inspect package state using the installed manager without refreshing metadata."""
    result: Dict[str, Any] = {"manager": "UNAVAILABLE", "updates": None, "broken": [], "reboot_required": False}
    if os.path.exists("/var/run/reboot-required"):
        result["reboot_required"] = True

    apt = shutil.which("apt")
    dpkg = shutil.which("dpkg")
    dnf = shutil.which("dnf")
    pacman = shutil.which("pacman")
    if apt:
        result["manager"] = "APT"
        code, output, _ = command_text([apt, "list", "--upgradable"], timeout=10)
        if code == 0:
            result["updates"] = sum("/" in line for line in output.splitlines())
        if dpkg:
            code, output, _ = command_text([dpkg, "--audit"], timeout=6)
            if code == 0:
                result["broken"] = [line.strip() for line in output.splitlines() if line.strip()][:10]
    elif dnf:
        result["manager"] = "DNF"
        code, output, _ = command_text([dnf, "check-update", "--cacheonly"], timeout=10)
        if code in (0, 100):
            result["updates"] = sum(bool(re.match(r"\S+\s+\S+\s+\S+", line)) for line in output.splitlines())
    elif pacman:
        result["manager"] = "Pacman"
        code, output, _ = command_text([pacman, "-Qu"], timeout=8)
        if code in (0, 1):
            result["updates"] = len([line for line in output.splitlines() if line.strip()])
    return result


def container_monitor() -> Dict[str, Any]:
    """Collect one-shot Docker/Podman container status and resource usage."""
    runtime = shutil.which("docker") or shutil.which("podman")
    result: Dict[str, Any] = {"runtime": None, "available": False, "containers": [], "error": None}
    if not runtime:
        return result
    result["runtime"] = os.path.basename(runtime)
    code, output, error = command_text(
        [runtime, "ps", "--format", "{{.Names}}|{{.Image}}|{{.Status}}"], timeout=6
    )
    if code != 0:
        result["error"] = error or "Container runtime is not available to this user"
        return result
    result["available"] = True
    containers: Dict[str, Dict[str, Any]] = {}
    for line in output.splitlines():
        name, image, status = (line.split("|", 2) + ["", ""])[:3]
        if name:
            containers[name] = {"name": name, "image": image, "status": status, "cpu": "-", "memory": "-", "memory_percent": "-", "network": "-"}

    code, output, _ = command_text(
        [runtime, "stats", "--no-stream", "--format", "{{.Name}}|{{.CPUPerc}}|{{.MemUsage}}|{{.MemPerc}}|{{.NetIO}}"], timeout=8
    )
    if code == 0:
        for line in output.splitlines():
            parts = line.split("|", 4)
            if len(parts) != 5:
                continue
            name, cpu, memory, memory_percent, network = parts
            item = containers.setdefault(name, {"name": name, "image": "?", "status": "?"})
            item.update({"cpu": cpu, "memory": memory, "memory_percent": memory_percent, "network": network})
    result["containers"] = list(containers.values())
    return result


def score_from_threshold(value: Optional[float], warning: float, critical: float) -> Optional[float]:
    if value is None:
        return None
    if value < warning:
        return 100.0
    if value >= critical:
        return 0.0
    return 100.0 * (critical - value) / max(critical - warning, 1.0)


def system_health_score(snapshot: Dict[str, Any]) -> Tuple[Dict[str, float], int]:
    """Return a transparent scorecard; unavailable diagnostics are not penalised."""
    scores: Dict[str, float] = {}
    cpu = snapshot.get("cpu", {})
    memory = snapshot.get("memory", {})
    disks = snapshot.get("disks", [])
    temperatures = snapshot.get("temperatures", [])
    scores["CPU"] = score_from_threshold(cpu.get("usage"), CPU_WARN, CPU_CRIT) or 0.0
    scores["MEMORY"] = score_from_threshold(memory.get("percent"), RAM_WARN, RAM_CRIT) or 0.0
    scores["SWAP"] = score_from_threshold(memory.get("swap_percent"), 50, 80) or 0.0
    scores["STORAGE"] = score_from_threshold(max((disk.get("percent", 0.0) for disk in disks), default=0.0), DISK_WARN, DISK_CRIT) or 0.0
    hottest = max((sensor.get("temp") for sensor in temperatures if sensor.get("temp") is not None), default=None)
    thermal = score_from_threshold(hottest, TEMP_WARN, TEMP_CRIT)
    if thermal is not None:
        scores["THERMALS"] = thermal
    network = score_from_threshold(snapshot.get("latency"), LAT_WARN, LAT_CRIT)
    if network is not None:
        scores["NETWORK"] = network

    disk_results = [item for item in snapshot.get("disk_health", []) if item.get("checked")]
    if disk_results:
        scores["DISK HEALTH"] = 100.0 - 50.0 * sum(item.get("health") == "CHECK" for item in disk_results)
        scores["DISK HEALTH"] = max(0.0, scores["DISK HEALTH"])
    security = snapshot.get("security", {})
    if security.get("firewall") != "UNKNOWN" or security.get("failed_auth") is not None:
        security_score = 100.0
        if security.get("firewall") == "INACTIVE":
            security_score -= 20.0
        security_score -= min(40.0, float(security.get("failed_auth") or 0) * 5.0)
        scores["SECURITY"] = max(0.0, security_score)
    kernel = snapshot.get("kernel_health", {})
    if kernel.get("available") or kernel.get("tainted"):
        scores["KERNEL"] = max(0.0, 100.0 - (15.0 if kernel.get("tainted") else 0.0) - min(55.0, kernel.get("oom", 0) * 20.0 + kernel.get("errors", 0) * 2.0))
    logs = snapshot.get("log_analysis", {})
    if logs.get("available"):
        scores["LOGS"] = max(0.0, 100.0 - min(75.0, logs.get("critical", 0) * 15.0 + logs.get("errors", 0) * 3.0 + logs.get("warnings", 0) * 0.5))
    packages = snapshot.get("package_health", {})
    if packages.get("updates") is not None:
        scores["PACKAGES"] = max(0.0, 100.0 - min(20.0, packages["updates"] * 0.5) - (50.0 if packages.get("broken") else 0.0))
    containers = snapshot.get("containers", {})
    if containers.get("available"):
        unhealthy = sum("unhealthy" in str(item.get("status", "")).lower() for item in containers.get("containers", []))
        scores["CONTAINERS"] = max(0.0, 100.0 - unhealthy * 35.0)

    total = round(sum(scores.values()) / len(scores)) if scores else 100
    return scores, total


def auto_diagnosis(snapshot: Dict[str, Any]) -> Tuple[List[str], List[str]]:
    """Turn the collected diagnostics into concise, actionable findings."""
    findings: List[str] = []
    recommendations: List[str] = []
    cpu = snapshot.get("cpu", {}).get("usage", 0.0)
    memory = snapshot.get("memory", {})
    if cpu >= CPU_WARN:
        findings.append(f"CPU load is high ({cpu:.1f}%).")
        recommendations.append("Inspect [9] TOP CPU PROCESSES.")
    if memory.get("percent", 0.0) >= RAM_WARN:
        findings.append(f"RAM use is high ({memory['percent']:.1f}%).")
        recommendations.append("Inspect [10] TOP RAM PROCESSES.")
    if memory.get("swap_percent", 0.0) >= 80:
        findings.append(f"Swap use is critical ({memory['swap_percent']:.1f}%).")
        recommendations.append("Close memory-heavy work or add RAM/swap capacity.")
    for disk in snapshot.get("disks", []):
        if disk.get("percent", 0.0) >= DISK_WARN:
            findings.append(f"Storage is filling: {disk['mount']} is {disk['percent']:.0f}% used.")
            recommendations.append(f"Free space on {disk['mount']}.")
    for disk in snapshot.get("disk_health", []):
        if disk.get("health") == "CHECK":
            findings.append(f"Disk health needs review: {disk['device']}.")
            recommendations.append("Review [12] DISK HEALTH; run SMART with appropriate privileges if needed.")
    failed = snapshot.get("failed_services") or []
    if failed:
        findings.append(f"{len(failed)} systemd service(s) have failed.")
        recommendations.append("Inspect [13] BOOT HEALTH and systemctl --failed.")
    security = snapshot.get("security", {})
    if security.get("firewall") == "INACTIVE":
        findings.append("Firewall is inactive.")
        recommendations.append("Review firewall policy before exposing services.")
    if (security.get("failed_auth") or 0) > 0:
        findings.append(f"{security['failed_auth']} authentication-failure indicator(s) were found.")
        recommendations.append("Review [14] SECURITY and relevant authentication logs.")
    kernel = snapshot.get("kernel_health", {})
    if kernel.get("tainted"):
        findings.append("Kernel is tainted.")
        recommendations.append("Check [15] KERNEL HEALTH for third-party module or kernel issues.")
    if kernel.get("oom", 0) > 0:
        findings.append(f"{kernel['oom']} kernel OOM event(s) were found in this boot.")
        recommendations.append("Review memory pressure and [16] LOG ANALYZER.")
    logs = snapshot.get("log_analysis", {})
    if logs.get("critical", 0) or logs.get("errors", 0):
        findings.append(f"Logs contain {logs.get('critical', 0)} critical and {logs.get('errors', 0)} error entries.")
        recommendations.append("Inspect the recent lines in [16] LOG ANALYZER.")
    packages = snapshot.get("package_health", {})
    if packages.get("broken"):
        findings.append("Package manager reports incomplete or broken package state.")
        recommendations.append("Repair package state with your distribution's package manager.")
    if packages.get("reboot_required"):
        findings.append("A reboot is required to complete installed updates.")
        recommendations.append("Schedule a reboot when it is safe to do so.")
    containers = snapshot.get("containers", {})
    unhealthy = [item["name"] for item in containers.get("containers", []) if "unhealthy" in str(item.get("status", "")).lower()]
    if unhealthy:
        findings.append(f"Unhealthy container(s): {', '.join(unhealthy[:3])}.")
        recommendations.append("Inspect [20] CONTAINER MONITOR and container logs.")
    if not findings:
        findings.append("No major issue was detected in the available diagnostics.")
        recommendations.append("Continue monitoring historical trends in [21].")
    return findings, recommendations


def historical_performance(history: List[Dict[str, Any]], current: Dict[str, Any]) -> Dict[str, Any]:
    """Summarise the current session without retaining data outside max_history."""
    samples = history + [current]

    def summary(values: List[float]) -> Dict[str, Any]:
        if not values:
            return {"current": None, "min": None, "average": None, "max": None, "trend": "N/A"}
        tail = values[-min(10, len(values)):]
        delta = tail[-1] - tail[0]
        trend = "RISING" if delta > 3 else "FALLING" if delta < -3 else "STEADY"
        return {
            "current": round(values[-1], 1),
            "min": round(min(values), 1),
            "average": round(sum(values) / len(values), 1),
            "max": round(max(values), 1),
            "trend": trend,
        }

    cpu_values = [float(item.get("cpu", {}).get("usage", 0.0)) for item in samples]
    ram_values = [float(item.get("memory", {}).get("percent", 0.0)) for item in samples]
    latency_values = [float(item["latency"]) for item in samples if item.get("latency") is not None]
    score_values = [float(item["health_score"]) for item in samples if item.get("health_score") is not None]
    return {
        "samples": len(samples),
        "from": samples[0].get("timestamp") if samples else None,
        "to": current.get("timestamp"),
        "cpu": summary(cpu_values),
        "memory": summary(ram_values),
        "latency": summary(latency_values),
        "health_score": summary(score_values),
    }


# Alerts builder
def alerts(cpu: Dict[str, Any], ram: Dict[str, Any], disks: List[Dict[str, Any]], temps: List[Dict[str, Any]], ping: Optional[float]) -> List[str]:
    a: List[str] = []
    if cpu.get("usage", 0.0) >= CPU_CRIT:
        a.append(f"CRITICAL: CPU {cpu['usage']:.1f}%")
    elif cpu.get("usage", 0.0) >= CPU_WARN:
        a.append(f"WARNING: CPU {cpu['usage']:.1f}%")
    if ram.get("percent", 0.0) >= RAM_CRIT:
        a.append(f"CRITICAL: RAM {ram['percent']:.1f}%")
    elif ram.get("percent", 0.0) >= RAM_WARN:
        a.append(f"WARNING: RAM {ram['percent']:.1f}%")
    for d in disks:
        if d.get("percent", 0.0) >= DISK_CRIT:
            a.append(f"CRITICAL: {d['mount']} {d['percent']:.0f}% full")
        elif d.get("percent", 0.0) >= DISK_WARN:
            a.append(f"WARNING: {d['mount']} {d['percent']:.0f}% full")
    for t in temps:
        value = t.get("temp")
        if value is None:
            continue
        critical = t.get("critical") or TEMP_CRIT
        high = t.get("high") or TEMP_WARN
        if value >= critical:
            a.append(f"CRITICAL: {t['name']} {value:.1f}°C")
        elif value >= high:
            a.append(f"WARNING: {t['name']} {value:.1f}°C")
    if ping is not None:
        if ping >= LAT_CRIT:
            a.append(f"CRITICAL: latency {ping:.0f} ms")
        elif ping >= LAT_WARN:
            a.append(f"WARNING: latency {ping:.0f} ms")
    return a


# Main encapsulation
class SysPulse:
    def __init__(
        self,
        refresh: float = DEFAULT_REFRESH,
        max_history: int = DEFAULT_MAX_HISTORY,
        ping_host: str = PING_HOST_DEFAULT,
        color: bool = True,
        notify_webhook: Optional[str] = None,
        diagnostic_interval: float = DEFAULT_DIAGNOSTIC_INTERVAL,
        container_interval: float = DEFAULT_CONTAINER_INTERVAL,
    ):
        self.refresh = float(refresh)
        self.max_history = int(max_history)
        self.ping_host = ping_host
        self.color = color
        self.diagnostic_interval = max(30.0, float(diagnostic_interval))
        self.container_interval = max(5.0, float(container_interval))
        self.history: List[Dict[str, Any]] = []
        self.net_prev = None
        self.disk_tracker = RateTracker()
        self.stop = False
        self.notify_webhook = notify_webhook
        self._diagnostic_cache: Dict[str, Tuple[float, Any]] = {}
        # Reusable executor to avoid creating many thread pools
        self.executor = ThreadPoolExecutor(max_workers=12)
        # Prime psutil CPU counters for accurate immediate readings
        psutil.cpu_percent(None)
        for p in psutil.process_iter():
            try:
                p.cpu_percent(None)
            except (psutil.NoSuchProcess, psutil.AccessDenied):
                pass

    def extended_diagnostics(self, now: float) -> Tuple[Dict[str, Any], Dict[str, float]]:
        """Refresh expensive, read-only probes only when their cache has expired."""
        probes = {
            "disk_health": (disk_health, self.diagnostic_interval, []),
            "boot_health": (boot_health, self.diagnostic_interval, {"available": False, "slow_services": []}),
            "security": (security_health, self.diagnostic_interval, {"firewall": "UNKNOWN"}),
            "kernel_health": (kernel_health, self.diagnostic_interval, {"available": False}),
            "log_analysis": (log_analyzer, self.diagnostic_interval, {"available": False, "recent": []}),
            "package_health": (package_health, self.diagnostic_interval, {"manager": "UNAVAILABLE", "updates": None, "broken": []}),
            "containers": (container_monitor, self.container_interval, {"runtime": None, "available": False, "containers": []}),
        }
        futures = {}
        values: Dict[str, Any] = {}
        ages: Dict[str, float] = {}
        for name, (probe, interval, fallback) in probes.items():
            cached = self._diagnostic_cache.get(name)
            if cached and now - cached[0] < interval:
                values[name] = cached[1]
                ages[name] = now - cached[0]
            else:
                futures[name] = (self.executor.submit(probe), fallback, cached)

        for name, (future, fallback, cached) in futures.items():
            try:
                value = future.result(timeout=12)
            except Exception:
                value = cached[1] if cached else fallback
            self._diagnostic_cache[name] = (now, value)
            values[name] = value
            ages[name] = 0.0
        return values, ages

    def snapshot(self) -> Dict[str, Any]:
        now = time.monotonic()
        # Submit probes to the shared executor for better performance
        tasks = {}
        tasks["battery"] = self.executor.submit(battery_info)
        tasks["sensors"] = self.executor.submit(sensors)
        tasks["storage"] = self.executor.submit(storage)
        tasks["net"] = self.executor.submit(lambda: network_rates(self.net_prev, now))
        tasks["disk_io_raw"] = self.executor.submit(psutil.disk_io_counters)
        tasks["latency"] = self.executor.submit(latency, self.ping_host)
        tasks["gpu"] = self.executor.submit(nvidia_gpu)
        tasks["process_stats"] = self.executor.submit(process_stats, 5)
        tasks["failed_services"] = self.executor.submit(failed_services)
        tasks["users"] = self.executor.submit(logged_users)

        results = {}
        for name, fut in tasks.items():
            try:
                results[name] = fut.result(timeout=3)
            except Exception:
                results[name] = None

        # Unpack network
        net_current, net_rates = results.get("net", (None, {}))
        if net_current is not None:
            self.net_prev = (net_current, now)

        # Disk IO rates (using disk_tracker)
        disk_io_raw = results.get("disk_io_raw")
        disk_rates = {"read": 0.0, "write": 0.0}
        if disk_io_raw is not None:
            disk_rates = self.disk_tracker.update(disk_io_raw, now, "read_bytes", "write_bytes")

        # Compose snapshot
        cpu = {
            "usage": psutil.cpu_percent(),
            "cores": psutil.cpu_percent(percpu=True),
            "logical": psutil.cpu_count(True),
            "physical": psutil.cpu_count(False),
            "freq": (psutil.cpu_freq().current if psutil.cpu_freq() else None),
        }
        ram = {
            "total": psutil.virtual_memory().total,
            "used": psutil.virtual_memory().used,
            "available": psutil.virtual_memory().available,
            "free": psutil.virtual_memory().free,
            "percent": psutil.virtual_memory().percent,
            "swap_total": psutil.swap_memory().total,
            "swap_used": psutil.swap_memory().used,
            "swap_percent": psutil.swap_memory().percent
        }

        temps, fans = results.get("sensors", ([], [])) or ([], [])
        disks = results.get("storage") or []
        ping = results.get("latency")
        gpu = results.get("gpu") or []
        top_cpu, top_ram, process_count, zombies = results.get("process_stats") or ([], [], 0, 0)
        failed = results.get("failed_services")
        users = results.get("users") or []
        diagnostics, diagnostic_ages = self.extended_diagnostics(now)

        snap = {
            "timestamp": datetime.now().isoformat(),
            "cpu": cpu,
            "memory": ram,
            "battery": results.get("battery"),
            "temperatures": temps,
            "fans": fans,
            "disks": disks,
            "network": net_rates,
            "disk_io": disk_rates,
            "latency": ping,
            "gpu": gpu,
            "top_cpu": top_cpu,
            "top_ram": top_ram,
            "process_count": process_count,
            "zombies": zombies,
            "failed_services": failed,
            "users": users,
            "disk_health": diagnostics["disk_health"],
            "boot_health": diagnostics["boot_health"],
            "security": diagnostics["security"],
            "kernel_health": diagnostics["kernel_health"],
            "log_analysis": diagnostics["log_analysis"],
            "package_health": diagnostics["package_health"],
            "containers": diagnostics["containers"],
            "diagnostic_ages": diagnostic_ages,
            "alerts": alerts(cpu, ram, disks, temps, ping),
        }
        score_breakdown, score = system_health_score(snap)
        snap["health_scores"] = score_breakdown
        snap["health_score"] = score
        snap["diagnosis"], snap["recommendations"] = auto_diagnosis(snap)
        snap["historical_performance"] = historical_performance(self.history, snap)
        return snap

    def notify_alerts(self, alerts: List[str]) -> None:
        if not alerts or not self.notify_webhook:
            return
        payload = {
            "generated": datetime.now().isoformat(),
            "host": socket.gethostname(),
            "alerts": alerts
        }
        def _post(url, body):
            try:
                import urllib.request, urllib.error
                req = urllib.request.Request(url, data=json.dumps(body).encode("utf-8"), headers={"Content-Type": "application/json"})
                with urllib.request.urlopen(req, timeout=5) as resp:
                    # consume response to avoid resource leak
                    resp.read()
            except Exception:
                # we silently ignore notify failures; logging could be added
                pass
        # submit to executor so notifications do not block the main loop
        try:
            self.executor.submit(_post, self.notify_webhook, payload)
        except Exception:
            pass

    def save_report(self, start_time: datetime, formats: Optional[List[str]] = None) -> None:
        formats = formats or ["txt", "json"]
        stamp = datetime.now().strftime("%d%m%Y_%H%M%S")
        duration = str(datetime.now() - start_time)
        txt = f"SysPulse_V9_1_{stamp}.txt"
        js = f"SysPulse_V9_1_{stamp}.json"
        report = {"generated": datetime.now().isoformat(), "duration": duration, "samples": self.history}
        try:
            if "json" in formats:
                with open(js, "w", encoding="utf-8") as f:
                    json.dump(report, f, indent=2, default=str)
            latest = self.history[-1] if self.history else {}
            if "txt" in formats:
                with open(txt, "w", encoding="utf-8") as f:
                    f.write("=== SYSPULSE ULTRA V9.1 REPORT ===\n\n")
                    f.write(f"Generated: {datetime.now()}\n")
                    f.write(f"Duration : {duration}\n")
                    f.write(f"Samples  : {len(self.history)}\n\n")
                    if latest:
                        c = latest.get("cpu", {})
                        m = latest.get("memory", {})
                        f.write("--- FINAL SYSTEM STATE ---\n")
                        f.write(f"CPU: {c.get('usage', 0.0):.1f}%\n")
                        f.write(f"RAM: {m.get('percent', 0.0):.1f}%\n")
                        f.write(f"Health Score: {latest.get('health_score', 'N/A')}/100\n")
                        f.write(f"Processes: {latest.get('process_count')}\n")
                        f.write(f"Zombies: {latest.get('zombies')}\n")
                        f.write(f"Latency: {latest.get('latency')}\n\n")
                        f.write("--- ALERTS ---\n")
                        if latest.get("alerts"):
                            for a in latest["alerts"]:
                                f.write(f"- {a}\n")
                        else:
                            f.write("No alerts.\n")
                        f.write("\n--- FAILED SERVICES ---\n")
                        if latest.get("failed_services"):
                            for x in latest["failed_services"]:
                                f.write(f"- {x}\n")
                        else:
                            f.write("No failed services detected.\n")
                        f.write("\n--- AUTO DIAGNOSIS ---\n")
                        for finding in latest.get("diagnosis") or ["No diagnosis available."]:
                            f.write(f"- {finding}\n")
                        f.write("\n--- PACKAGE HEALTH ---\n")
                        package = latest.get("package_health") or {}
                        f.write(f"Manager: {package.get('manager', 'UNAVAILABLE')}\n")
                        f.write(f"Updates: {package.get('updates', 'N/A')}\n")
                        f.write(f"Reboot required: {package.get('reboot_required', False)}\n")
            if "html" in formats:
                hfile = f"SysPulse_V9_1_{stamp}.html"
                try:
                    with open(hfile, "w", encoding="utf-8") as f:
                        f.write('<!doctype html>\n<html><head><meta charset="utf-8"><title>SysPulse Report</title></head><body>')
                        f.write(f"<h1>SysPulse Ultra Report - {datetime.now()}</h1>")
                        f.write(f"<p>Duration: {duration} | Samples: {len(self.history)}</p>")
                        if latest:
                            f.write('<h2>Final System State</h2>')
                            f.write('<ul>')
                            c = latest.get('cpu', {})
                            m = latest.get('memory', {})
                            f.write(f"<li>CPU: {c.get('usage', 0.0):.1f}%</li>")
                            f.write(f"<li>RAM: {m.get('percent', 0.0):.1f}%</li>")
                            f.write(f"<li>Health score: {latest.get('health_score', 'N/A')}/100</li>")
                            f.write(f"<li>Processes: {latest.get('process_count')}</li>")
                            f.write(f"<li>Zombies: {latest.get('zombies')}</li>")
                            f.write('</ul><h2>Auto Diagnosis</h2><ul>')
                            for finding in latest.get('diagnosis') or ['No diagnosis available.']:
                                f.write(f"<li>{finding}</li>")
                            f.write('</ul>')
                        f.write('</body></html>')
                    print(f"{Fore.GREEN}[✓] HTML: {hfile}")
                except Exception:
                    pass
            if "txt" in formats:
                print(f"\n{Fore.GREEN}[✓] TXT: {txt}")
            if "json" in formats:
                print(f"{Fore.GREEN}[✓] JSON: {js}")
            # Send notification if requested and alerts present
            latest_alerts = (self.history[-1].get('alerts') if self.history else [])
            if latest_alerts:
                self.notify_alerts(latest_alerts)
        except Exception as e:
            print(f"Failed to write report: {e}", file=sys.stderr)

    def dashboard(self, s: Dict[str, Any]) -> None:
        if sys.stdout.isatty():
            os.system("clear" if os.name != "nt" else "cls")
        cpu = s["cpu"]
        ram = s["memory"]
        bat = s.get("battery")
        print(Fore.CYAN + "╔" + "═" * 78 + "╗")
        title = "SYSPULSE ULTRA V9.1"
        print(Fore.CYAN + "║" + Fore.WHITE + Style.BRIGHT + title.center(78) + Fore.CYAN + "║")
        print("╚" + "═" * 78 + "╝")
        print(f"{Fore.YELLOW}[1] SYSTEM")
        print(f"OS       : {os.uname().sysname} {os.uname().release}" if hasattr(os, "uname") else f"OS: {sys.platform}")
        print(f"HOST     : {socket.gethostname()}")
        try:
            import getpass
            user = getpass.getuser()
        except Exception:
            user = "?"
        print(f"USER     : {user}")
        print(f"CPU      : {cpu.get('physical') or '?'} Physical / {cpu.get('logical') or '?'} Logical")
        print(f"UPTIME   : {uptime(time.time() - psutil.boot_time())}")
        print(f"PROCESSES: {s.get('process_count')} | ZOMBIES: {s.get('zombies')}")
        load = getattr(os, "getloadavg", lambda: None)()
        if load:
            print(f"LOAD     : {load[0]:.2f} | {load[1]:.2f} | {load[2]:.2f}")
        print(f"USERS    : {len(s.get('users') or [])}")
        # CPU
        print(f"\n{Fore.YELLOW}[2] CPU")
        ccol = col(cpu.get("usage", 0.0), CPU_WARN, CPU_CRIT)
        print(f"TOTAL    : {ccol}[{bar(cpu.get('usage', 0.0))}] {cpu.get('usage', 0.0):.1f}%")
        if cpu.get("freq"):
            print(f"FREQUENCY: {cpu['freq'] / 1000.0:.2f} GHz")
        for i, value in enumerate(cpu.get("cores", [])[:32], 1):
            print(f"CORE {i:02d}  : {col(value, CPU_WARN, CPU_CRIT)}[{bar(value, 15)}] {value:.1f}%")
        # MEMORY
        print(f"\n{Fore.YELLOW}[3] MEMORY")
        c = col(ram.get("percent", 0.0), RAM_WARN, RAM_CRIT)
        print(f"RAM      : {c}[{bar(ram.get('percent', 0.0))}] {ram.get('percent', 0.0):.1f}%")
        print(f"USED     : {size(ram.get('used'))} / {size(ram.get('total'))}")
        print(f"AVAILABLE: {size(ram.get('available'))}")
        print(f"SWAP     : {ram.get('swap_percent', 0.0):.1f}% ({size(ram.get('swap_used'))} / {size(ram.get('swap_total'))})")
        # BATTERY
        print(f"\n{Fore.YELLOW}[4] BATTERY")
        if not bat:
            print("Battery   : N/A")
        else:
            state = "Charging" if bat.get("charging") else "On Battery"
            print(f"CHARGE   : {bat.get('percent', 0.0):.0f}% [{state}]")
            secs = bat.get("seconds_left")
            print(f"TIME LEFT: {uptime(secs) if isinstance(secs, (int, float)) else 'Unknown'}")
            if "health" in bat:
                print(f"HEALTH   : {bat['health']:.1f}%")
        # THERMALS
        print(f"\n{Fore.YELLOW}[5] THERMALS")
        if s.get("temperatures"):
            for t in s["temperatures"][:8]:
                print(f"{t['name'][:18]:<18}: {col(t['temp'], TEMP_WARN, TEMP_CRIT)}{t['temp']:.1f}°C")
        else:
            print("Temperature sensors unavailable.")
        if s.get("fans"):
            for fan in s["fans"][:5]:
                print(f"{fan['name'][:18]:<18}: {fan['rpm']} RPM")
        # STORAGE
        print(f"\n{Fore.YELLOW}[6] STORAGE")
        rows = []
        for d in s.get("disks", []):
            rows.append([d["device"], d["mount"], d["type"], size(d["total"]), size(d["free"]), f"{d['percent']:.0f}%"])
        if rows and tabulate:
            print(tabulate(rows, headers=["Device", "Mount", "FS", "Capacity", "Free", "Used"], tablefmt="simple_grid"))
        else:
            for r in rows:
                print(" | ".join(map(str, r)))
        print(f"READ     : {size(s.get('disk_io', {}).get('read'))}/s")
        print(f"WRITE    : {size(s.get('disk_io', {}).get('write'))}/s")
        # NETWORK
        print(f"\n{Fore.YELLOW}[7] NETWORK")
        addresses = ipv4_addresses()
        rows = []
        for name, info in (s.get("network") or {}).items():
            rows.append([name, addresses.get(name, "N/A"), f"{size(info['down'])}/s", f"{size(info['up'])}/s", info["rx"], info["tx"], info["rx_err"], info["tx_err"]])
        if rows and tabulate:
            print(tabulate(rows, headers=["Interface", "IPv4", "Down", "Up", "RX", "TX", "RX Err", "TX Err"], tablefmt="simple_grid"))
        else:
            for r in rows:
                print(" | ".join(map(str, r)))
        if s.get("latency") is None:
            print(f"INTERNET : {Fore.RED}Offline / Unknown")
        else:
            lc = col(s.get("latency"), LAT_WARN, LAT_CRIT)
            print(f"LATENCY  : {lc}{s.get('latency'):.0f} ms")
        # GPU
        print(f"\n{Fore.YELLOW}[8] GPU")
        if s.get("gpu"):
            for i, g in enumerate(s["gpu"], 1):
                print(f"GPU {i}    : {g['name']}")
                print(f"  TEMP    : {g['temp']:.0f}°C")
                print(f"  USAGE   : {g['usage']:.0f}%")
                print(f"  VRAM    : {g['vram_used']:.0f}/{g['vram_total']:.0f} MB")
                print(f"  POWER   : {g['power']:.1f} W")
        else:
            print("NVIDIA GPU unavailable.")
        # TOP CPU
        print(f"\n{Fore.YELLOW}[9] TOP CPU PROCESSES")
        rows = [[p["pid"], p["name"][:22], f"{p['cpu']:.1f}%", f"{p['ram']:.1f}%"] for p in s.get("top_cpu", [])]
        if rows and tabulate:
            print(tabulate(rows, headers=["PID", "Process", "CPU", "RAM"], tablefmt="simple_grid"))
        else:
            for r in rows:
                print(" | ".join(map(str, r)))
        # TOP RAM
        print(f"\n{Fore.YELLOW}[10] TOP RAM PROCESSES")
        rows = [[p["pid"], p["name"][:22], f"{p['ram']:.1f}%", f"{p['cpu']:.1f}%"] for p in s.get("top_ram", [])]
        if rows and tabulate:
            print(tabulate(rows, headers=["PID", "Process", "RAM", "CPU"], tablefmt="simple_grid"))
        else:
            for r in rows:
                print(" | ".join(map(str, r)))
        # LINUX HEALTH
        print(f"\n{Fore.YELLOW}[11] LINUX HEALTH")
        health_rows = []
        if s.get("failed_services") is None:
            health_rows.append(["SYSTEMD", "Not available"])
        else:
            health_rows.append(["SYSTEMD", f"{len(s.get('failed_services') or [])} failed service(s)"])
            for service in (s.get("failed_services") or [])[:3]:
                health_rows.append(["!", service])
        health_rows.append(["ZOMBIES", s.get("zombies")])
        if tabulate:
            print(tabulate(health_rows, headers=["Check", "Result"], tablefmt="simple_grid"))
        else:
            for row in health_rows:
                print(" | ".join(map(str, row)))
        # DISK HEALTH
        print(f"\n{Fore.YELLOW}[12] DISK HEALTH")
        disk_details = s.get("disk_health") or []
        if disk_details:
            rows = [
                [
                    item.get("device", "?"),
                    str(item.get("model", "Unknown"))[:20],
                    item.get("type", "?"),
                    item.get("health", "?"),
                    f"{item['temperature']:.0f}°C" if item.get("temperature") is not None else "-",
                    f"{item['wear']:.0f}%" if item.get("wear") is not None else "-",
                    item.get("media_errors") if item.get("media_errors") is not None else "-",
                ]
                for item in disk_details
            ]
            if tabulate:
                print(tabulate(rows, headers=["Device", "Model", "Type", "Health", "Temp", "Wear", "Errors"], tablefmt="simple_grid"))
            else:
                for row in rows:
                    print(" | ".join(map(str, row)))
        else:
            print("SMART/NVMe data unavailable (the utility may be missing or need permission).")
        print(f"CACHE AGE: {s.get('diagnostic_ages', {}).get('disk_health', 0):.0f}s")
        # BOOT HEALTH
        print(f"\n{Fore.YELLOW}[13] BOOT HEALTH")
        boot = s.get("boot_health") or {}
        boot_rows = []
        if boot.get("available"):
            for label, key in (("BOOT TIME", "boot_time"), ("KERNEL", "kernel_time"), ("USERSPACE", "userspace_time")):
                value = boot.get(key)
                shown = f"{value:.2f}s" if isinstance(value, (int, float)) else "N/A"
                boot_rows.append([label, shown])
            if boot.get("slow_services"):
                for service in boot["slow_services"][:5]:
                    boot_rows.append(["SLOW", service])
        else:
            boot_rows.append(["STATUS", "systemd-analyze is unavailable on this system."])
        if tabulate:
            print(tabulate(boot_rows, headers=["Metric", "Value"], tablefmt="simple_grid"))
        else:
            for row in boot_rows:
                print(" | ".join(map(str, row)))
        # SECURITY
        print(f"\n{Fore.YELLOW}[14] SECURITY")
        security = s.get("security") or {}
        listening = security.get("listening_ports")
        failed_auth = security.get("failed_auth")
        root_processes = security.get("root_processes")
        print(f"FIREWALL : {security.get('firewall', 'UNKNOWN')}")
        print(f"PORTS    : {listening if listening is not None else 'N/A'} listening")
        print(f"SSH      : {security.get('ssh', 'UNKNOWN')}")
        print(f"FAILED   : {failed_auth if failed_auth is not None else 'N/A'} auth indicator(s)")
        print(f"ROOT     : {root_processes if root_processes is not None else 'N/A'} root process(es)")
        # KERNEL HEALTH
        print(f"\n{Fore.YELLOW}[15] KERNEL HEALTH")
        kernel = s.get("kernel_health") or {}
        print(f"VERSION  : {kernel.get('version', 'N/A')}")
        print(f"TAINTED  : {'YES' if kernel.get('tainted') else 'NO'} ({kernel.get('taint', 'UNKNOWN')})")
        print(f"MODULES  : {kernel.get('modules') if kernel.get('modules') is not None else 'N/A'}")
        print(f"OOM      : {kernel.get('oom', 0)}")
        print(f"ERRORS   : {kernel.get('errors', 0)}")
        print(f"WARNINGS : {kernel.get('warnings', 0)}")
        # LOG ANALYZER
        print(f"\n{Fore.YELLOW}[16] LOG ANALYZER")
        logs = s.get("log_analysis") or {}
        if logs.get("available"):
            print(f"CRITICAL : {logs.get('critical', 0)}")
            print(f"ERRORS   : {logs.get('errors', 0)}")
            print(f"WARNINGS : {logs.get('warnings', 0)}")
            if logs.get("recent"):
                print("RECENT:")
                for line in logs["recent"][-4:]:
                    print(f"  {line[:120]}")
        else:
            print("Current-boot journal data is unavailable.")
        # SYSTEM HEALTH SCORE
        print(f"\n{Fore.YELLOW}[17] SYSTEM HEALTH SCORE")
        score = s.get("health_score", 100)
        status = "EXCELLENT" if score >= 90 else "GOOD" if score >= 75 else "WARNING" if score >= 50 else "CRITICAL"
        print(f"TOTAL    : {score}/100 ({status})")
        score_rows = [[name, f"{value:.1f}/100"] for name, value in (s.get("health_scores") or {}).items()]
        if score_rows and tabulate:
            print(tabulate(score_rows, headers=["Component", "Score"], tablefmt="simple_grid"))
        else:
            for row in score_rows:
                print(f"{row[0]:<14}: {row[1]}")
        # AUTO DIAGNOSIS
        print(f"\n{Fore.YELLOW}[18] AUTO DIAGNOSIS")
        for finding in s.get("diagnosis") or ["No diagnosis available."]:
            print(f"  >> {finding}")
        recommendations = s.get("recommendations") or []
        if recommendations:
            print("RECOMMEND:")
            for recommendation in recommendations[:5]:
                print(f"  >> {recommendation}")
        # UPDATE / PACKAGE HEALTH
        print(f"\n{Fore.YELLOW}[19] UPDATE / PACKAGE HEALTH")
        packages = s.get("package_health") or {}
        updates = packages.get("updates")
        print(f"MANAGER  : {packages.get('manager', 'UNAVAILABLE')}")
        print(f"UPDATES  : {updates if updates is not None else 'N/A'}")
        print(f"REBOOT   : {'REQUIRED' if packages.get('reboot_required') else 'Not required'}")
        if packages.get("broken"):
            print("PACKAGE STATE:")
            for item in packages["broken"][:3]:
                print(f"  ! {item[:110]}")
        else:
            print("PACKAGE STATE: No incomplete packages reported.")
        # CONTAINER MONITOR
        print(f"\n{Fore.YELLOW}[20] CONTAINER MONITOR")
        containers = s.get("containers") or {}
        runtime = containers.get("runtime")
        if not runtime:
            print("No Docker or Podman runtime detected.")
        elif not containers.get("available"):
            print(f"{runtime}: {containers.get('error') or 'runtime unavailable'}")
        else:
            container_rows = [
                [item.get("name", "?"), str(item.get("image", "?"))[:24], str(item.get("status", "?"))[:28], item.get("cpu", "-"), item.get("memory", "-"), item.get("network", "-")]
                for item in containers.get("containers", [])
            ]
            print(f"RUNTIME  : {runtime}")
            if container_rows and tabulate:
                print(tabulate(container_rows, headers=["Name", "Image", "Status", "CPU", "Memory", "Network"], tablefmt="simple_grid"))
            elif container_rows:
                for row in container_rows:
                    print(" | ".join(map(str, row)))
            else:
                print("No running containers.")
            print(f"CACHE AGE: {s.get('diagnostic_ages', {}).get('containers', 0):.0f}s")
        # HISTORICAL PERFORMANCE
        print(f"\n{Fore.YELLOW}[21] HISTORICAL PERFORMANCE")
        historical = s.get("historical_performance") or {}
        print(f"SAMPLES  : {historical.get('samples', 0)} (up to {self.max_history} retained)")
        history_rows = []
        for label, key in (("CPU", "cpu"), ("MEMORY", "memory"), ("LATENCY", "latency"), ("HEALTH SCORE", "health_score")):
            values = historical.get(key) or {}
            if values.get("current") is None:
                history_rows.append([label, "N/A", "N/A", "N/A", "N/A", values.get("trend", "N/A")])
            else:
                history_rows.append([label, values["current"], values["min"], values["average"], values["max"], values["trend"]])
        if tabulate:
            print(tabulate(history_rows, headers=["Metric", "Now", "Min", "Avg", "Max", "Trend"], tablefmt="simple_grid"))
        else:
            for row in history_rows:
                print(" | ".join(map(str, row)))
        # ALERTS
        if s.get("alerts"):
            print(f"\n{Fore.RED}{Style.BRIGHT}[!] ALERTS")
            for alert in s.get("alerts"):
                print(f"  >> {alert}")
        else:
            print(f"\n{Fore.GREEN}[✓] SYSTEM STATUS: NORMAL")
        print(Fore.CYAN + "\n" + "═" * 80)
        print(Fore.WHITE + f"{datetime.now():%H:%M:%S} | Ctrl+C = export report")

    def run(self) -> None:
        start = datetime.now()
        try:
            while not self.stop:
                data = self.snapshot()
                self.history.append(data)
                if len(self.history) > self.max_history:
                    self.history.pop(0)
                self.dashboard(data)
                time.sleep(self.refresh)
        except KeyboardInterrupt:
            self.stop = True
        finally:
            print(Fore.YELLOW + "\n\nStopping SysPulse...")
            # Allow caller to set preferred report formats via sp.report_formats
            self.save_report(start, formats=getattr(self, 'report_formats', None))
            try:
                self.executor.shutdown(wait=False)
            except Exception:
                pass
            print(Fore.CYAN + "Goodbye.")


# CLI and signal handling
def parse_args():
    p = argparse.ArgumentParser(description="SysPulse Ultra v9.1")
    p.add_argument("--refresh", "-r", type=float, default=DEFAULT_REFRESH, help="Refresh interval in seconds")
    p.add_argument("--max-history", "-m", type=int, default=DEFAULT_MAX_HISTORY, help="Max history samples to keep")
    p.add_argument("--host", "-H", default=PING_HOST_DEFAULT, help="Host to ping for latency")
    p.add_argument("--no-color", action="store_true", help="Disable colored output")
    p.add_argument("--once", action="store_true", help="Take a single snapshot and exit (useful for cron)" )
    p.add_argument("--export-format", "-e", default="txt,json", help="Comma-separated export formats: txt,json,html")
    p.add_argument("--notify-webhook", "-n", default=None, help="URL to POST alerts to when critical conditions appear")
    p.add_argument("--diagnostic-interval", type=float, default=DEFAULT_DIAGNOSTIC_INTERVAL, help="Seconds between disk, boot, security, kernel, log, and package checks (minimum 30)")
    p.add_argument("--container-interval", type=float, default=DEFAULT_CONTAINER_INTERVAL, help="Seconds between container checks (minimum 5)")
    return p.parse_args()


def main():
    args = parse_args()
    if args.no_color:
        disable_color_output()
    if args.refresh <= 0 or args.max_history < 1:
        raise SystemExit("--refresh must be positive and --max-history must be at least one")
    if args.diagnostic_interval < 30 or args.container_interval < 5:
        raise SystemExit("--diagnostic-interval must be at least 30 and --container-interval at least 5")
    # parse export formats into list
    formats = [x.strip().lower() for x in (args.export_format or "").split(",") if x.strip()]
    sp = SysPulse(
        refresh=args.refresh,
        max_history=args.max_history,
        ping_host=args.host,
        color=not args.no_color,
        notify_webhook=args.notify_webhook,
        diagnostic_interval=args.diagnostic_interval,
        container_interval=args.container_interval,
    )
    # attach desired report formats to the instance so run() will use them
    sp.report_formats = formats if formats else None

    def _signal_handler(signum, frame):
        sp.stop = True

    signal.signal(signal.SIGINT, _signal_handler)
    try:
        signal.signal(signal.SIGTERM, _signal_handler)
    except Exception:
        pass

    if args.once:
        # take one snapshot and save according to requested formats
        start = datetime.now()
        snap = sp.snapshot()
        sp.history.append(snap)
        sp.dashboard(snap)
        sp.save_report(start, formats=sp.report_formats)
        try:
            sp.executor.shutdown(wait=False)
        except Exception:
            pass
        return

    sp.run()


if __name__ == "__main__":
    main()
