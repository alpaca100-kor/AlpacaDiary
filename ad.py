"""
알파카 다이어리 (Alpaca Diary) — ad.py

일반메모 / 달력메모 / 체크리스트 / 컬렉션 네 개의 탭으로 이루어진 메모 앱. 각 탭은 독립적인
데이터 파일(memos.json / memos_calendar.json / checklists.json / collections.json)을 갖고,
공통 UI 요소(글꼴/테마/단축키 등)는 공유한다.
"""

import tkinter as tk
from tkinter import messagebox, filedialog, simpledialog, Toplevel, font, ttk
import json
import os
import re
import sys
import uuid
import queue
import threading
import html
import webbrowser
import configparser
import bisect
import shutil
import zipfile
import codecs
import hashlib
from urllib.parse import urlparse
from datetime import datetime, date, timedelta
import calendar

# 엑셀 파일 처리를 위한 라이브러리. (없으면 엑셀 내보내기 비활성화)
try:
    import openpyxl
    from openpyxl.cell.cell import ILLEGAL_CHARACTERS_RE
except ImportError:
    openpyxl = None
    ILLEGAL_CHARACTERS_RE = None

# Windows 11 스타일(Sun Valley) ttk 테마. (없으면 기본 ttk 테마로 동작)
try:
    import sv_ttk
except ImportError:
    sv_ttk = None

# URL 제목 자동 가져오기(컬렉션 탭)에 사용. (없으면 그 기능만 비활성화)
try:
    import requests
except ImportError:
    requests = None


def resource_path(relative_path):
    """PyInstaller로 생성된 exe의 리소스 경로를 가져옴"""
    try:
        base_path = sys._MEIPASS
    except Exception:
        base_path = os.path.abspath(".")
    return os.path.join(base_path, relative_path)


def get_app_dir():
    """실행 파일(exe) 또는 스크립트가 있는 폴더 경로를 반환함.

    사용자 데이터(memos.json, settings.ini 등)는 실행할 때의 작업 디렉터리(cwd)와 상관없이
    항상 같은 위치에 저장해야 하므로 이 함수를 씀. resource_path()의 sys._MEIPASS는
    onefile 실행 시 임시 폴더라 종료하면 사라지므로 데이터 경로에는 쓰면 안 됨.
    """
    if getattr(sys, "frozen", False):
        # PyInstaller로 빌드된 exe: exe 파일이 있는 폴더
        return os.path.dirname(sys.executable)
    # 일반 .py 스크립트로 실행되는 경우: 스크립트 파일이 있는 폴더
    return os.path.dirname(os.path.abspath(__file__))


_single_instance_handle = None  # 프로세스가 끝날 때까지 뮤텍스 핸들을 붙잡아 둠 (OS가 종료 시 자동 해제)


def acquire_single_instance(app_dir):
    """같은 폴더(app_dir)의 알파카 다이어리가 이미 실행 중이면 False, 아니면 True를 반환함.
    둘이 동시에 떠 있으면 서로의 변경을 모른 채 나중에 닫는 쪽이 파일을 덮어쓰기 때문에 막음.

    Windows의 이름 있는 뮤텍스를 쓰며, 이름에 폴더 경로의 해시를 넣어서 다른 폴더에 둔 사본은
    따로 실행할 수 있음. 비Windows이거나 확인 자체가 실패하면 실행을 막지 않고 True를 반환함."""
    global _single_instance_handle
    if sys.platform != "win32":
        return True
    try:
        import ctypes
        kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
        kernel32.CreateMutexW.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_wchar_p]
        kernel32.CreateMutexW.restype = ctypes.c_void_p
        key = hashlib.sha1(os.path.normcase(os.path.abspath(app_dir)).encode("utf-8")).hexdigest()[:16]
        handle = kernel32.CreateMutexW(None, False, f"Local\\AlpacaDiary_{key}")
        if not handle:
            return True
        if ctypes.get_last_error() == 183:  # ERROR_ALREADY_EXISTS: 다른 프로세스가 이미 만들어 둠
            return False
        _single_instance_handle = handle
        return True
    except Exception:
        return True


def set_windows_app_id(app_id="alpaca.diary"):
    """Windows 작업표시줄이 이 프로그램을 python/pythonw 등 다른 프로그램과 묶지 않고
    독립된 앱으로 인식하도록 AppUserModelID를 지정함. 창 아이콘이 작업표시줄에도 제대로
    표시되려면 tk.Tk()를 만들기 전에 호출해야 함. Windows가 아니거나 API가 없으면 조용히 무시함."""
    if sys.platform != "win32":
        return
    try:
        import ctypes
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(app_id)
    except Exception:
        pass


def normalize_url(raw):
    """스킴이 없는 URL에 https://를 붙여 정규화함 (컬렉션 탭)"""
    raw = raw.strip()
    if raw and not re.match(r"^[a-zA-Z][a-zA-Z0-9+.\-]*://", raw):
        raw = "https://" + raw
    return raw


# Excel 셀 하나에 넣을 수 있는 최대 글자 수
XLSX_MAX_CELL_CHARS = 32767


def append_xlsx_row(ws, row):
    """워크시트에 한 행을 추가함. 메모 내용이 Excel에서 그대로 보이도록 다음을 처리하고,
    글자 수 제한 때문에 잘린 셀의 개수를 반환함.
    - '='로 시작하는 문자열(예: "==== 메모 ====")은 openpyxl이 수식으로 저장해 Excel에서 오류가
      나므로 문자열 셀로 고정함
    - Excel이 허용하지 않는 제어문자(세로탭 등)는 openpyxl이 예외를 내므로 제거함
    - 한 셀 최대 글자 수(XLSX_MAX_CELL_CHARS)를 넘으면 잘라냄"""
    truncated = 0
    values = []
    for value in row:
        if isinstance(value, str):
            value = ILLEGAL_CHARACTERS_RE.sub("", value)
            if len(value) > XLSX_MAX_CELL_CHARS:
                value = value[:XLSX_MAX_CELL_CHARS]
                truncated += 1
        values.append(value)
    ws.append(values)
    for cell in ws[ws.max_row]:
        if isinstance(cell.value, str):
            cell.data_type = "s"
    return truncated


def now_iso():
    return datetime.now().isoformat(timespec="seconds")


def short_id():
    return str(uuid.uuid4())


def set_text_content(widget, text=""):
    """코드로 Text 위젯의 내용을 통째로 바꾸고 실행취소 기록을 비움.
    Tk는 누가 바꿨는지 구분하지 않고 코드의 delete/insert도 기록하므로, 메모를 전환할 때 비우지
    않으면 Ctrl+Z가 다른 메모의 내용(또는 빈 내용)을 되살리고, 키 입력 자동저장이 그것을 현재
    메모에 저장해 버림. 그래서 내용을 코드로 채울 때는 항상 이 함수를 써야 함."""
    widget.delete("1.0", tk.END)
    widget.insert("1.0", text)
    widget.edit_reset()


def bind_redo_shortcuts(widget):
    """다시 실행(Redo)을 Ctrl+Y와 Ctrl+Shift+Z로 통일함. Tk의 기본 단축키는 플랫폼마다 달라서
    (X11은 Ctrl+Shift+Z, Windows는 Ctrl+Y) 직접 연결하며, "break"로 기본 바인딩이 한 번 더
    실행되어 두 단계가 다시 실행되는 일을 막음. (취소는 모든 플랫폼에서 기본 Ctrl+Z)"""
    def redo(event):
        try:
            widget.edit_redo()
        except tk.TclError:
            pass  # 다시 실행할 기록이 없음
        return "break"
    for sequence in ("<Control-y>", "<Control-Y>", "<Control-Z>"):
        widget.bind(sequence, redo)


def insert_text_as_one_undo_step(widget, text):
    """선택 영역이 있으면 지우고 text를 커서 위치에 넣되, (삭제+삽입) 전체가 Ctrl+Z 한 번에 취소되고
    앞뒤 타이핑과도 섞이지 않도록 하나의 실행취소 묶음으로 기록함. (autoseparators는 삭제↔삽입이
    바뀔 때 묶음을 나누므로, 이 작업 동안만 꺼 둠)"""
    widget.edit_separator()
    widget.configure(autoseparators=False)
    try:
        try:
            widget.delete("sel.first", "sel.last")
        except tk.TclError:
            pass  # 선택 영역이 없음
        widget.insert(tk.INSERT, text)
    finally:
        widget.configure(autoseparators=True)
    widget.edit_separator()


def unique_id(raw, seen):
    """파일에서 읽은 id를 문자열로 바꿔 반환하되, 비어 있거나 seen에 이미 있으면(직접 편집한
    파일 등에서 중복) 새 id를 만듦. Treeview는 같은 id의 행을 두 번 넣으면 TclError가 남.
    반환한 id는 seen에 기록함."""
    value = str(raw or "")
    if not value or value in seen:
        value = short_id()
    seen.add(value)
    return value


# MemoStore._read_json이 "읽을 데이터가 없음(파일 없음/빈 파일/손상)"을 알리는 표지.
# None은 JSON의 null과 구분되지 않으므로 별도 객체를 씀
NO_DATA = object()

_DATE_KEY_RE = re.compile(r"(\d{4})-(\d{1,2})-(\d{1,2})")


def normalize_date_key(raw):
    """날짜 문자열을 달력이 조회하는 "YYYY-MM-DD"(0 채움) 형태로 바꿔 반환함. "2026-9-5"도
    "2026-09-05"로 바로잡음 (strptime은 0이 빠진 형태도 통과시키므로 쓰지 않음).
    문자열이 아니거나, 형식이 다르거나, 없는 날짜이거나, 달력이 지원하는 연도
    (CAL_MIN_YEAR~CAL_MAX_YEAR) 밖이면 None."""
    if not isinstance(raw, str):
        return None
    m = _DATE_KEY_RE.fullmatch(raw.strip())
    if not m:
        return None
    year, month, day = (int(g) for g in m.groups())
    if not (CAL_MIN_YEAR <= year <= CAL_MAX_YEAR):
        return None
    try:
        date(year, month, day)
    except ValueError:
        return None
    return f"{year:04d}-{month:02d}-{day:02d}"


def normalize_calendar_memos(data):
    """{날짜: 내용} 딕셔너리의 날짜 키를 정규화함. (정규화된 딕셔너리, 건너뛴 키 목록)을 반환.
    날짜가 올바르지 않거나 내용이 문자열이 아닌 항목은 건너뛰고, 정규화한 날짜가 겹치는 항목
    ("2026-9-5"와 "2026-09-05")은 내용을 합쳐 어느 쪽도 잃지 않게 함."""
    result, skipped = {}, []
    for key, content in data.items():
        norm = normalize_date_key(key)
        if norm is None or not isinstance(content, str):
            skipped.append(key)
            continue
        result[norm] = f"{result[norm]}\n\n{content}" if norm in result else content
    return result, skipped


def is_web_url(url):
    """브라우저로 열어도 되는 http/https 주소인지. file://, javascript: 같은 다른 스킴은
    OS 기본 프로그램으로 넘어갈 수 있어 열지 않음"""
    try:
        parsed = urlparse(url.strip())
    except (ValueError, AttributeError):
        return False
    return parsed.scheme.lower() in ("http", "https") and bool(parsed.netloc)


class EmptyTransferFileError(Exception):
    """가져오기/복원할 JSON 파일이 비어 있을 때 (구조 오류와 다른 안내문을 보여주기 위함)"""


def bind_when_visible(widget, sequence, callback):
    """widget.bind(sequence, callback)과 같지만, 그 위젯이 화면에서 사라져 있을 때는
    callback을 실행하지 않음.

    탭/서브탭을 전환해도 키보드 포커스는 옮겨지지 않아서, 화면에서 사라진 목록/입력창이
    포커스를 그대로 갖고 있고 키 입력도 계속 거기로 전달됨. 가드가 없으면 다른 탭을 보는
    중에 PageUp/PageDown이나 Delete가 안 보이는 목록에 적용됨.

    안 보일 때는 None을 반환해 키를 그대로 통과시킴("break"를 반환하면 root에 걸린 전역
    단축키까지 막힘). 보이는 동안은 callback의 반환값("break" 등)을 그대로 돌려줌.
    winfo_viewable()은 위젯과 모든 부모가 map된 상태일 때만 True라서, 노트북에서 다른 탭에
    가려진 위젯은 False가 됨.
    """
    def handler(event):
        if not widget.winfo_viewable():
            return None
        return callback(event)
    return widget.bind(sequence, handler)


def restore_listbox_top(listbox, old_ids, old_top, new_ids):
    """Listbox를 지웠다가 다시 채운 뒤, 다시 그리기 전에 보던 위치로 스크롤을 되돌림.
    (다시 그리면 스크롤이 맨 위로 초기화됨)

    - old_ids/new_ids: 다시 그리기 전/후의 각 행이 어떤 항목(id)인지 (표시 순서대로)
    - old_top: 다시 그리기 전에 맨 위에 보이던 행 번호 (Listbox.nearest(0)), 목록이 비어
      있었다면 None
    행 수가 같으면(순서 이동/이름 변경/단순 재그리기) 맨 위 행 번호를 그대로 쓰고, 행 수가
    달라졌으면(추가/삭제) 맨 위에 보이던 항목의 id로 새 위치를 찾아서 보던 내용이 밀리지
    않게 함 (그 항목이 사라졌다면 이전 행 번호를 씀). 선택 행이 화면 밖이면 호출한 쪽이
    이어서 see()로 보이게 하면 됨."""
    if old_top is None or not new_ids:
        return
    if len(new_ids) == len(old_ids):
        top = old_top
    else:
        anchor = old_ids[old_top] if 0 <= old_top < len(old_ids) else None
        top = new_ids.index(anchor) if anchor in new_ids else old_top
    listbox.yview(max(0, min(top, len(new_ids) - 1)))


def replace_listbox_row(listbox, index, text):
    """Listbox의 한 행 글자만 바꿈 (전체를 다시 그리지 않음 - 스크롤/나머지 행은 그대로).
    delete+insert를 하면 그 행의 선택 표시가 사라지고 활성(active) 항목이 한 칸 밀리므로
    원래 상태로 되돌림."""
    was_selected = listbox.selection_includes(index)
    active = listbox.index("active")
    listbox.delete(index)
    listbox.insert(index, text)
    if was_selected:
        listbox.selection_set(index)
    listbox.activate(active)


def focus_listbox_edge(listbox, to_end):
    """Home/End 키용: Listbox의 첫 번째(to_end=False) 또는 마지막(to_end=True) 항목을
    선택하고, 방향키 탐색의 기준인 활성(active) 항목으로 지정하고, 화면에 보이도록
    스크롤함. 항목이 없으면 아무 것도 하지 않음. 이동한 인덱스(없으면 None)를 반환함.

    - Listbox의 기본 Home/End는 가로 스크롤일 뿐이므로, 이 함수를 부르는 키 핸들러는
      "break"를 반환해 기본 동작을 막아야 함.
    - selection_set()/activate()는 <<ListboxSelect>>를 발생시키지 않음. 방향키로 옮길 때와
      같은 처리(오른쪽 목록/편집창 갱신 등)가 실행되도록, 선택이 실제로 바뀐 경우에만
      이벤트를 직접 발생시킴.
    - 화면에서 사라진 목록에서는 동작하지 않아야 하므로, 키 바인딩은 bind_when_visible로
      거는 것을 전제로 함.
    """
    size = listbox.size()
    if size == 0:
        return None
    target = size - 1 if to_end else 0
    changed = tuple(listbox.curselection()) != (target,)
    listbox.selection_clear(0, tk.END)
    listbox.selection_set(target)
    listbox.activate(target)
    listbox.see(target)
    if changed:
        listbox.event_generate("<<ListboxSelect>>")
    return target


def focus_tree_edge(tree, to_end):
    """Home/End 키용: Treeview의 첫 번째(to_end=False) 또는 마지막(to_end=True) 항목을
    선택하고 포커스 항목으로 지정한 뒤 화면에 보이도록 스크롤함. 항목이 없으면 아무 것도
    하지 않음. 이동한 항목 id(없으면 None)를 반환함.

    Treeview는 방향키 탐색의 기준이 선택이 아니라 포커스(focus) 항목이라 focus()까지
    지정해야 이후 ↑↓가 그 위치에서 이어짐. (<<TreeviewSelect>>는 selection_set()이 선택을
    바꿀 때 Tk가 발생시킴.) Treeview에는 기본 Home/End 동작이 없지만 키 핸들러는 일관되게
    "break"를 반환함. 키 바인딩은 focus_listbox_edge와 같이 bind_when_visible로 건다.
    """
    children = tree.get_children()
    if not children:
        return None
    target = children[-1] if to_end else children[0]
    tree.selection_set(target)
    tree.focus(target)
    tree.see(target)
    return target


# 일반 UI 라벨/입력창에 쓰는 공통 글꼴. 사용자 설정 대상이 아니고(설정 가능한 것은
# 메모 내용 글꼴 content_font뿐) 실행 중 바뀌지 않으므로 모듈 상수로 둠
UI_FONT = ("맑은 고딕", 12)

# 본문 글꼴 크기 허용 범위 (글꼴 설정창 입력 검사와 settings.ini 로드에서 함께 사용)
FONT_SIZE_MIN = 8
FONT_SIZE_MAX = 72

# 빠른 입력(Alt+1~Alt+0) 슬롯 키 순서: 1,2,...,9,0
QUICK_INPUT_KEYS = [str(i) for i in range(1, 10)] + ["0"]

# 실시간 자동저장 디바운스 지연시간(ms): 이 시간 안에 새 키 입력이 있으면 저장을 다시
# 미루고, 입력이 멈추고 이 시간이 지나야 실제로 디스크에 씀. (컬렉션/체크리스트 탭은
# 추가/삭제/편집 확정 같은 불연속 동작으로만 바뀌므로 디바운스 없이 즉시 저장함)
AUTOSAVE_DEBOUNCE_MS = 500

# 되돌릴 수 없는 작업(가져오기/복원/달력메모 일괄삭제) 직전에 만드는 자동 백업:
# 앱 폴더 아래 AUTO_BACKUP_DIRNAME 폴더에 ZIP으로 남기고, 최근 AUTO_BACKUP_KEEP개만 보관함
AUTO_BACKUP_DIRNAME = "backup_auto"
AUTO_BACKUP_PREFIX = "AlpacaDiary_auto_"
AUTO_BACKUP_KEEP = 10

# 본문 Text 위젯의 실행취소(Ctrl+Z, 다시실행 Ctrl+Y) 설정. Tk가 입력/삭제를 묶음 단위로 기록하며
# (autoseparators: 입력↔삭제가 바뀔 때마다 묶음을 나눔), 기록이 메모리를 무한정 쓰지 않도록 상한을 둠
TEXT_UNDO_OPTIONS = {"undo": True, "autoseparators": True, "maxundo": 1000}

# 백업 ZIP 안의 파일 하나당 읽을 수 있는 최대 크기(바이트). 손상되었거나 악의적으로 만든
# ZIP이 메모리를 과도하게 쓰지 않도록 막는 안전장치 (일반적인 메모 데이터는 이보다 훨씬 작음)
MAX_BACKUP_MEMBER_BYTES = 100 * 1024 * 1024

# 달력메모 탭 달력의 날짜 칸(Canvas) 크기(px)
CAL_CELL_W = 40
CAL_CELL_H = 34
# 달력메모 탭 왼쪽(달력) 영역의 고정 폭(px) - 월별보기/1년전체보기/목록보기 폭을 통일하고,
# 사용자가 크기조절 막대로 바꿀 수 없도록 PanedWindow 대신 고정폭 Frame에 사용
CAL_LEFT_WIDTH = 360
# 달력(월별/1년전체 보기)이 지원하는 연도 범위. 연도 입력창 범위이자 달력메모 날짜의 허용 범위
# (범위 밖 연도는 date 계산에서 예외가 나므로 입력 단계에서 막음)
CAL_MIN_YEAR = 1900
CAL_MAX_YEAR = 2100

# Windows 가상 키코드(VK_0~VK_9) -> 숫자 문자열 매핑
# (<Alt-1> 같은 개별 keysym 바인딩이 Windows에서 씹히는 문제를 우회하기 위해
#  <Alt-KeyPress>로 받은 뒤 keycode로 눌린 키를 직접 판별하는 데 사용)
ALT_DIGIT_VK_CODES = {48: "0", 49: "1", 50: "2", 51: "3", 52: "4",
                       53: "5", 54: "6", 55: "7", 56: "8", 57: "9"}

# [도움말] 메뉴의 바로가기 링크 (기본 웹 브라우저로 열림)
PROGRAM_INFO_URL = "https://github.com/alpaca100-kor/AlpacaDiary"
ALPACA_TOOLS_URL = "https://alpaca100-kor.github.io/AlpacaTools/"
AUTHOR_BLOG_URL = "https://alpaca100.tistory.com/"

# [도움말 > 단축키 안내](F1) 창에 보여줄 내용이 들어 있는 파일 이름. 안내 문구는 코드가 아니라
# 이 파일에만 두며, 프로그램(exe 또는 ad.py)과 같은 폴더에서 창을 열 때마다 읽음 (exe에는
# 포함시키지 않음). 작성 규칙은 shortcuts.md 맨 위 주석 참고
SHORTCUTS_FILE_NAME = "shortcuts.md"

# 다크/라이트 테마별 색상 팔레트 (sv_ttk의 실제 팔레트 값 기준). ttk가 직접 테마를 입히지
# 못하는 Listbox/Text/Treeview 인라인편집 위젯에 수동으로 적용하기 위함
THEME_COLORS = {
    "light": {
        "bg": "#fafafa",
        "fg": "#1c1c1c",
        "border": "#e0e0e0",
        "accent": "#005fb8",
        "list_select_bg": "#0067c0",
        "list_select_fg": "#ffffff",
        "text_select_bg": "#2f60d8",
        "text_select_fg": "#ffffff",
        "insert_bg": "#1c1c1c",
        "disabled_bg": "#f3f3f3",
        "success_fg": "#0067c0",
        "sunday_fg": "#c42b1c",
        "muted_fg": "#9a9a9a",
        "has_memo_bg": "#cfe3f7",
    },
    "dark": {
        "bg": "#1c1c1c",
        "fg": "#fafafa",
        "border": "#3a3a3a",
        "accent": "#57c8ff",
        "list_select_bg": "#0067c0",
        "list_select_fg": "#ffffff",
        "text_select_bg": "#2f60d8",
        "text_select_fg": "#ffffff",
        "insert_bg": "#fafafa",
        "disabled_bg": "#252525",
        "success_fg": "#ffd600",
        "sunday_fg": "#ff8a80",
        "muted_fg": "#6b6b6b",
        "has_memo_bg": "#1c3a52",
    },
}


def apply_titlebar_theme(root, dark):
    """Windows 10/11에서 창 제목표시줄 색상까지 다크모드에 맞춤.
    Windows가 아니거나 API를 지원하지 않으면 조용히 무시함(다른 OS 크래시 방지)."""
    try:
        import ctypes
        root.update_idletasks()

        hwnd = ctypes.windll.user32.GetParent(root.winfo_id())
        if not hwnd:
            # GetParent로 못 찾으면 창 제목으로 실제 최상위 창을 직접 검색 (폴백)
            hwnd = ctypes.windll.user32.FindWindowW(None, root.title())
        if not hwnd:
            return

        DWMWA_USE_IMMERSIVE_DARK_MODE = 20
        value = ctypes.c_int(1 if dark else 0)
        ctypes.windll.dwmapi.DwmSetWindowAttribute(
            hwnd, DWMWA_USE_IMMERSIVE_DARK_MODE, ctypes.byref(value), ctypes.sizeof(value)
        )

        # DwmSetWindowAttribute만으로는 이미 화면에 떠 있는 창의 타이틀바가
        # 곧바로 다시 그려지지 않는 경우가 있어, 프레임을 강제로 한 번 갱신시켜준다.
        SWP_NOMOVE, SWP_NOSIZE, SWP_NOZORDER, SWP_FRAMECHANGED = 0x0002, 0x0001, 0x0004, 0x0020
        ctypes.windll.user32.SetWindowPos(
            hwnd, 0, 0, 0, 0, 0,
            SWP_NOMOVE | SWP_NOSIZE | SWP_NOZORDER | SWP_FRAMECHANGED
        )
    except Exception:
        pass


# ============================================================================
# 앱 구조 안내 (탭을 추가하려는 유지보수자를 위해)
# ----------------------------------------------------------------------------
# MemoStore        : 파일 입출력만 담당 (tkinter 위젯을 전혀 모름). memos /
#                    calendar_memos / collections / checklists / settings /
#                    quick_inputs / holidays 를 읽고 씀.
# SettingsManager  : 설정 상태(글꼴/복사단축키/테마/빠른입력) 보유 + 설정 팝업들.
# GeneralMemoTab   : "일반메모" 탭 전체(위젯+데이터+동작).
# CalendarMemoTab  : "달력메모" 탭 전체(위젯+데이터+동작).
# ChecklistTab     : "체크리스트" 탭 전체(위젯+데이터+동작). CollectionTab과 같은
#                    UI/조작 방식(왼쪽 폴더 목록 + 오른쪽 항목, 인라인 편집, 드래그
#                    순서변경)에 항목을 완료 여부+내용으로 단순화함.
# CollectionTab    : "컬렉션" 탭 전체(위젯+데이터+동작). 컬렉션/항목 CRUD, URL 제목
#                    자동 수집, 순서 변경. 이미지 첨부 기능은 없음.
# MemoApp          : 위를 조립하는 지휘자. 메뉴/전역 단축키/창 생명주기/
#                    테마·상태표시줄처럼 "탭을 넘나드는" 것만 여기 남김.
#
# 새 탭을 추가하려면:
#   1) 위 탭 클래스들처럼 새 클래스를 만들고 __init__(self, parent, app)에서
#      parent(ttk.Frame) 위에 UI를 구성한다.
#   2) 아래 메서드를 구현하면 MemoApp이 알아서 호출해준다.
#        [필수 4개]
#        - apply_theme_colors(self, colors)   : 테마(라이트/다크) 변경 시
#        - set_content_font(self, font_tuple) : "글꼴 설정"에서 내용 글꼴 변경 시
#        - get_status_text(self)              : 상태표시줄에 표시할 문자열
#        - get_copy_target(self)              : (복사할 내용, 복사완료라벨) 또는 None
#                                               복사할 내용 = 텍스트위젯, 또는 복사할 문자열을
#                                               돌려주는 함수 (복사 버튼/단축키가 공통으로 사용)
#        [선택 - 구현한 탭이 활성화되어 있을 때만 호출됨]
#        - on_activated(self, event=None) / on_deactivated(self, event=None)
#        - on_ctrl_n(self, event=None) / on_ctrl_d(self, event=None)
#        - focus_content(self, event=None)    : Ctrl+M
#        - focus_primary(self, event=None)    : Ctrl+T
#        - focus_list(self, event=None)       : Ctrl+L
#        - on_page_up(self, event=None) / on_page_down(self, event=None)
#        - insert_text_at_widget(self, widget, text) -> bool  : Alt+T / Alt+숫자
#        [선택 - 파일 메뉴의 가져오기/내보내기/전체 백업·복원에 참여하려면]
#        - transfer_label / transfer_filename : 탭 이름(예: "달력메모") / 데이터 파일명
#                                               (예: "memos_calendar.json" - 백업 ZIP 안의 이름)
#        - transfer_parse(raw) -> data        : 가져온 JSON을 검증/정규화 (잘못되면 TypeError/ValueError)
#        - transfer_apply(data) -> bool       : 데이터를 교체하고 저장·화면 갱신 (저장 성공 여부 반환)
#        - transfer_summary(data) -> str      : 복원 확인창에 보여줄 요약 (예: "메모 12개")
#        - transfer_export_json() -> data     : 내보내기/백업에 쓸 현재 데이터
#        - transfer_export_txt() -> str       : TXT 내보내기 내용 (보관·열람용)
#        - transfer_export_xlsx() -> (시트 이름, 머리글 리스트, 행 리스트)  (보관·열람용)
#        파일 선택/확인창/형식별 저장 흐름은 MemoApp(import_current_tab 등)이 모든 탭에 공통으로
#        처리하므로, 탭이 늘어나도 파일 메뉴 항목 수는 늘지 않고 메뉴 코드를 고칠 필요도 없음.
#   3) MemoApp.__init__에서 notebook에 프레임을 추가하고 self.tabs 리스트에 넣는다.
#      (self.tabs의 순서는 반드시 notebook.add() 순서와 같아야 함)
#   4) 이 탭에서만 쓰는 전용 단축키(예: 컬렉션/체크리스트의 Ctrl+Shift+N, 달력메모의
#      Alt+H)는, 그 이름의 메서드를 이 탭에만 만들고 MemoApp.__init__에
#      self.root.bind("<키>", ...)를 한 줄 추가한다 (아래 MemoApp의 "탭 전용 단축키"
#      절 참고). Delete/Enter/Space/F2처럼 "그 위젯에 포커스가 있을 때만" 동작해야
#      하는 키는 root가 아니라 그 위젯에 직접 bind()하면 되고, 그러면 다른 탭과
#      자동으로 격리되므로 이런 라우터가 필요 없다.
#
# 활성 탭을 하드코딩해서 확인하지 않는 이유:
#   "일반메모가 아니면 달력메모" 같은 가정은 탭이 늘면 깨진다(예: 컬렉션 탭에서 Ctrl+D가
#   달력메모 삭제를 실행함). 그래서 "활성 탭에 그 이름의 메서드가 있으면 호출하고, 없으면
#   아무 일도 하지 않는다"는 방식으로 라우팅한다. 탭이 몇 개로 늘어도 그대로 동작한다.
# ============================================================================


class WriteBlockedError(OSError):
    """시작할 때 읽지 못한 파일을 덮어쓰지 않으려고 저장을 막았을 때 발생 (MemoStore.write_blocked)"""


class MemoStore:
    """memos.json / memos_calendar.json / collections.json / checklists.json /
    settings.ini / quick_inputs.json / holidays.json 파일 입출력만 담당. tkinter
    위젯을 전혀 참조하지 않으므로 GUI 없이도 단위 테스트가 가능함. 저장할 데이터는
    항상 인자로 받고(self가 데이터를 들고 있지 않음), 읽은 데이터는 검증해서 반환하며,
    읽는 중 생긴 안내 문구만 load_problems/holiday_problems에 모아 둠."""

    def __init__(self, app_dir):
        self.app_dir = app_dir
        self.file_path = os.path.join(app_dir, "memos.json")
        self.settings_file = os.path.join(app_dir, "settings.ini")
        self.quick_input_file = os.path.join(app_dir, "quick_inputs.json")
        self.calendar_file_path = os.path.join(app_dir, "memos_calendar.json")
        self.holiday_file = os.path.join(app_dir, "holidays.json")
        self.collections_file = os.path.join(app_dir, "collections.json")
        self.checklists_file = os.path.join(app_dir, "checklists.json")
        # 시작할 때 읽지 못했거나 일부를 건너뛴 데이터 파일 안내 문구 (시작 후 MemoApp이 한 번 보여줌)
        self.load_problems = []
        # 열지 못해서(사용 중/권한) 빈 데이터로 시작한 파일의 경로. 종료할 때의 자동 저장이 읽지 못한
        # 원본을 빈 데이터로 덮어쓰지 않도록, 이 경로에는 쓰지 않음 (_atomic_write 참고)
        self.write_blocked = set()
        # 가장 최근 _atomic_write의 실패 원인(성공하면 None). 저장 실패 팝업에 사유를 보여주는 데 씀
        self.last_write_error = None

    def _atomic_write(self, path, write_func):
        """write_func(파일객체)로 내용을 쓰되, 같은 폴더의 임시 파일에 먼저 쓴 뒤 os.replace()로
        교체하는 원자적 저장. os.replace()는 이름만 바꾸는 연산이라 OS가 원자적으로 처리하므로,
        쓰는 도중 앱이 강제 종료되거나 오류가 나도 원본 파일(path)은 손상되지 않음.
        (원자성을 보장하려면 임시 파일이 같은 폴더에 있어야 함)"""
        if path in self.write_blocked:
            self.last_write_error = WriteBlockedError(
                f"{os.path.basename(path)} 파일을 읽지 못한 채 시작해서 덮어쓰지 않습니다. "
                "프로그램을 다시 실행해 주세요.")
            raise self.last_write_error
        tmp_path = path + ".tmp"
        try:
            with open(tmp_path, "w", encoding="utf-8") as f:
                write_func(f)
            os.replace(tmp_path, path)
            self.last_write_error = None
        except Exception as e:
            self.last_write_error = e
            # 어떤 예외든 원본은 아직 손대지 않았으므로 안전함. 남은 임시 파일만 정리하고
            # 예외는 그대로 위로 전달함
            try:
                if os.path.exists(tmp_path):
                    os.remove(tmp_path)
            except OSError:
                pass
            raise

    def _atomic_write_json(self, path, data):
        """JSON 데이터를 원자적으로 저장 (_atomic_write 참고)"""
        self._atomic_write(path, lambda f: json.dump(data, f, ensure_ascii=False, indent=4))

    def write_json(self, path, data):
        """내보내기용: 임의 경로에 JSON을 원자적으로 저장 (실패하면 예외를 그대로 전달)"""
        self._atomic_write_json(path, data)

    def write_backup_zip(self, path, files):
        """files({ZIP 안의 파일명: 텍스트 내용})를 ZIP 하나로 묶어 path에 저장.
        _atomic_write와 같은 이유로 임시 파일에 먼저 만든 뒤 os.replace()로 교체하므로,
        저장 도중 실패해도 기존에 있던 같은 이름의 백업 파일은 손상되지 않음."""
        tmp_path = path + ".tmp"
        try:
            with zipfile.ZipFile(tmp_path, "w", zipfile.ZIP_DEFLATED) as zf:
                for name, text in files.items():
                    zf.writestr(name, text.encode("utf-8"))
            os.replace(tmp_path, path)
        except Exception:
            try:
                if os.path.exists(tmp_path):
                    os.remove(tmp_path)
            except OSError:
                pass
            raise

    def write_auto_backup(self, files, reason, keep=AUTO_BACKUP_KEEP):
        """되돌릴 수 없는 작업 직전의 데이터를 앱 폴더의 AUTO_BACKUP_DIRNAME 폴더에 ZIP으로 남기고,
        오래된 자동 백업은 최근 keep개만 남기고 지움. 만든 파일의 경로를 반환함.
        실패하면 예외를 그대로 전달함 (호출한 쪽이 계속할지 사용자에게 물음)."""
        folder = os.path.join(self.app_dir, AUTO_BACKUP_DIRNAME)
        os.makedirs(folder, exist_ok=True)
        stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        path = os.path.join(folder, f"{AUTO_BACKUP_PREFIX}{reason}_{stamp}.zip")
        number = 2
        while os.path.exists(path):  # 같은 초에 두 번 만들어도 기존 백업을 덮어쓰지 않음
            path = os.path.join(folder, f"{AUTO_BACKUP_PREFIX}{reason}_{stamp}_{number}.zip")
            number += 1
        self.write_backup_zip(path, files)
        self._prune_auto_backups(folder, keep)
        return path

    @staticmethod
    def _prune_auto_backups(folder, keep):
        """folder 안의 자동 백업(AUTO_BACKUP_PREFIX로 시작하는 .zip)만 최근 keep개 남기고 지움.
        정리에 실패해도 백업 자체는 이미 만들어졌으므로 무시함."""
        try:
            names = [n for n in os.listdir(folder)
                     if n.startswith(AUTO_BACKUP_PREFIX) and n.endswith(".zip")]
            names.sort(key=lambda n: (os.path.getmtime(os.path.join(folder, n)), n), reverse=True)
            for old in names[keep:]:
                os.remove(os.path.join(folder, old))
        except OSError:
            pass

    def read_backup_zip(self, path, names):
        """백업 ZIP에서 names(파일명 집합)에 해당하는 파일을 읽어 {파일명: 텍스트}로 반환.
        폴더째 압축한 ZIP도 읽을 수 있도록 경로의 마지막 이름만 비교하며, ZIP 안의 파일을
        디스크에 풀지 않고 메모리에서만 읽음 (그래서 경로 조작 같은 위험이 없음).
        ZIP이 아니면 zipfile.BadZipFile, 파일이 너무 크면 ValueError를 발생시킴."""
        result = {}
        with zipfile.ZipFile(path, "r") as zf:
            for info in zf.infolist():
                if info.is_dir():
                    continue
                base = info.filename.replace("\\", "/").rsplit("/", 1)[-1]
                if base in names and base not in result:
                    if info.file_size > MAX_BACKUP_MEMBER_BYTES:
                        raise ValueError(f"{base} 파일이 너무 큽니다.")
                    result[base] = zf.read(info).decode("utf-8-sig")
        return result

    def _preserve_original(self, path, reason, move=True):
        """읽은 데이터가 원본과 달라질 때(손상으로 빈 데이터로 시작하거나, 일부 항목을 건너뜀) 원본을
        같은 폴더에 남겨 둠. 남기지 않으면 종료할 때의 자동 저장이 원본을 덮어써 영영 사라짐.
        move=True면 원본을 ".corrupt-시각"으로 옮기고, False면 ".skipped-시각"으로 복사함."""
        stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
        base = f"{path}.{'corrupt' if move else 'skipped'}-{stamp}"
        dest, n = base, 1
        while os.path.exists(dest):  # 같은 초에 두 번 보관해도 먼저 보관한 파일을 덮어쓰지 않음
            n += 1
            dest = f"{base}-{n}"
        try:
            if move:
                os.replace(path, dest)
            else:
                shutil.copy2(path, dest)
            note = f"원본을 '{os.path.basename(dest)}' 파일로 보관했습니다."
        except OSError:
            note = "원본 보관에 실패했습니다. 프로그램을 끝내기 전에 이 파일을 직접 복사해 두세요."
        self.load_problems.append(f"{os.path.basename(path)}: {reason}\n  → {note}")

    def _read_json(self, path, check, quarantine=True):
        """JSON 파일을 읽어 반환함. 읽을 데이터가 없으면 NO_DATA를 반환함 (호출한 쪽이 기본값 사용).

        - BOM이 붙은 UTF-8(메모장 저장 등)도 읽음.
        - 파일이 없거나 내용이 비어 있으면 안내 없이 NO_DATA.
        - 손상(JSON/UTF-8 아님)이거나 check(data)가 False(예상한 구조가 아님)면 NO_DATA를 반환하고,
          quarantine=True면 원본을 보관한 뒤 load_problems에 안내를 남김. 앱이 쓰지 않는 참고용
          파일(holidays.json)은 quarantine=False로 불러 원본을 그대로 둠.
        - 파일을 열지 못하는 경우(권한/사용 중)는 원본을 건드리지 않고 안내를 남기며, 빈 데이터로 시작한
          뒤 원본을 덮어쓰지 않도록 그 경로의 저장을 막음(write_blocked). 참고용 파일(quarantine=False)은
          어차피 쓰지 않으므로 안내만 남김."""
        if not os.path.exists(path):
            return NO_DATA
        name = os.path.basename(path)

        def reject(reason):
            if quarantine:
                self._preserve_original(path, reason)
            else:
                self.load_problems.append(f"{name}: {reason}\n  → 이 파일은 읽기만 하므로 그대로 두었습니다.")
            return NO_DATA

        try:
            with open(path, "r", encoding="utf-8-sig") as f:
                text = f.read()
            if not text.strip():
                return NO_DATA
            data = json.loads(text)
        except OSError as e:
            message = f"{name}: 파일을 읽지 못했습니다 ({e.__class__.__name__})."
            if quarantine:
                self.write_blocked.add(path)
                message += ("\n  → 원본이 빈 데이터로 덮어써지지 않도록 이 파일은 저장하지 않습니다."
                            "\n    다른 프로그램이 파일을 사용 중인지 확인한 뒤 프로그램을 다시 실행해 주세요.")
            self.load_problems.append(message)
            return NO_DATA
        except (UnicodeDecodeError, json.JSONDecodeError):
            return reject("올바른 JSON(UTF-8) 파일이 아니라서 읽지 못했습니다.")
        if not check(data):
            return reject("예상한 데이터 구조가 아니라서 읽지 못했습니다.")
        return data

    def load_memos(self):
        data = self._read_json(self.file_path, lambda d: isinstance(d, list))
        if data is NO_DATA:
            return []
        # title/content 키가 없거나 문자열이 아닌 항목이 섞여 있어도 이후 코드가 KeyError로
        # 죽지 않도록 여기서 구조를 정규화함
        return [{"title": str(memo.get("title", "")), "content": str(memo.get("content", ""))}
                for memo in data if isinstance(memo, dict)]

    def save_memos(self, memos):
        try:
            self._atomic_write_json(self.file_path, memos)
            return True
        except Exception as e:
            print(f"❌ 메모 저장 실패: {e}")
            return False

    def load_holidays(self):
        """대한민국 공휴일을 holidays.json에서 불러옴 (없거나 손상되었으면 빈 딕셔너리).
        {"YYYY-MM-DD": "공휴일 이름"} 형태이며, 앱이 쓰지는 않는 참고용 파일이라 최신 연도를
        쓰려면 직접 교체/추가해야 함. 직접 편집하다 생긴 오타가 달력/목록에 영향을 주지 않도록
        항목마다 검증해(날짜는 normalize_date_key, 이름은 비어 있지 않은 문자열) 올바른 것만
        쓰고, 건너뛴 항목은 self.holiday_problems에 기록함(시작 후 한 번 안내함)."""
        self.holiday_problems = []
        data = self._read_json(self.holiday_file, lambda d: isinstance(d, dict), quarantine=False)
        if data is NO_DATA:
            return {}
        holidays = {}
        for key, name in data.items():
            norm = normalize_date_key(key)
            if norm is None:
                self.holiday_problems.append(
                    f"{key!r}: 올바른 날짜(YYYY-MM-DD, {CAL_MIN_YEAR}~{CAL_MAX_YEAR}년)가 아닙니다")
                continue
            if not isinstance(name, str) or not name.strip():
                self.holiday_problems.append(f"{key}: 공휴일 이름이 비어 있거나 문자열이 아닙니다")
                continue
            holidays[norm] = name.strip()
        return holidays

    def load_calendar_memos(self):
        """달력메모(memos_calendar.json)를 불러옴: {"YYYY-MM-DD": "내용", ...} 형태.
        가져오기(CalendarMemoTab.transfer_parse)와 같은 normalize_calendar_memos로 검증함.
        건너뛴 항목이 있으면 원본을 복사해 두고 시작 후 안내함."""
        data = self._read_json(self.calendar_file_path, lambda d: isinstance(d, dict))
        if data is NO_DATA:
            return {}
        memos, skipped = normalize_calendar_memos(data)
        if skipped:
            self._preserve_original(
                self.calendar_file_path,
                f"날짜 형식이 올바르지 않거나 내용이 문자열이 아닌 항목 {len(skipped)}개를 건너뛰었습니다.",
                move=False)
        return memos

    def save_calendar_memos(self, calendar_memos):
        try:
            self._atomic_write_json(self.calendar_file_path, dict(sorted(calendar_memos.items())))
            return True
        except Exception as e:
            print(f"❌ 달력메모 저장 실패: {e}")
            return False

    def load_quick_inputs(self):
        """Alt+1~Alt+0에 대응하는 빠른 입력 문구를 불러옴 (없으면 전부 빈 문자열)"""
        data = self._read_json(self.quick_input_file, lambda d: isinstance(d, dict))
        if data is NO_DATA:
            return {key: "" for key in QUICK_INPUT_KEYS}
        return {key: (data[key] if isinstance(data.get(key), str) else "") for key in QUICK_INPUT_KEYS}

    def save_quick_inputs(self, quick_inputs):
        try:
            self._atomic_write_json(self.quick_input_file, quick_inputs)
            return True
        except Exception as e:
            print(f"❌ 빠른 입력 저장 실패: {e}")
            return False

    def load_settings(self):
        config = configparser.ConfigParser()
        default_settings = {
            'font_family': '맑은 고딕',
            'font_size': 12,
            'window_geometry': '800x600+100+100',
            'copy_shortcut': 'Ctrl+Shift+C',
            'theme_mode': 'light',
            'show_holidays_in_list': False
        }

        if not os.path.exists(self.settings_file):
            return default_settings

        try:
            config.read(self.settings_file, encoding='utf-8-sig')
            font_family = config.get('Font', 'family', fallback=default_settings['font_family'])
            font_size = config.getint('Font', 'size', fallback=default_settings['font_size'])
            if not (FONT_SIZE_MIN <= font_size <= FONT_SIZE_MAX):
                # 범위를 벗어난 값(손상/직접 편집)은 기본값으로 되돌림
                font_size = default_settings['font_size']
            window_geometry = config.get('Window', 'geometry', fallback=default_settings['window_geometry'])
            copy_shortcut = config.get('Shortcuts', 'copy', fallback=default_settings['copy_shortcut'])
            theme_mode = config.get('Theme', 'mode', fallback=default_settings['theme_mode'])
            if theme_mode not in ("light", "dark"):
                theme_mode = default_settings['theme_mode']
            show_holidays_in_list = config.getboolean(
                'Calendar', 'show_holidays_in_list', fallback=default_settings['show_holidays_in_list'])
            return {
                'font_family': font_family,
                'font_size': font_size,
                'window_geometry': window_geometry,
                'copy_shortcut': copy_shortcut,
                'theme_mode': theme_mode,
                'show_holidays_in_list': show_holidays_in_list
            }
        except (configparser.Error, ValueError):
            return default_settings

    def save_settings(self, settings):
        """settings: font_family/font_size/window_geometry/copy_shortcut/theme_mode/
        show_holidays_in_list 키를 모두 가진 딕셔너리 (SettingsManager.save()가 조립해서 넘김)"""
        config = configparser.ConfigParser()
        config['Font'] = {
            'family': settings.get('font_family', '맑은 고딕'),
            'size': str(settings.get('font_size', 12))
        }
        config['Window'] = {
            'geometry': settings.get('window_geometry', '800x600+100+100')
        }
        config['Shortcuts'] = {
            'copy': settings.get('copy_shortcut', 'Ctrl+Shift+C')
        }
        config['Theme'] = {
            'mode': settings.get('theme_mode', 'light')
        }
        config['Calendar'] = {
            'show_holidays_in_list': str(bool(settings.get('show_holidays_in_list', False)))
        }
        try:
            self._atomic_write(self.settings_file, config.write)
            print(f"✅ 설정 저장: {settings.get('window_geometry')}")
            return True
        except Exception as e:
            print(f"❌ 설정 저장 실패: {e}")
            return False

    def load_collections(self):
        """collections.json 로드: {"collections": [{"id","name","created",
        "items":[{"id","title","url","memo","added"}]}]} 형태. 파일이 없거나 손상되었으면
        빈 컬렉션 목록을 반환하고(손상이면 원본은 보관), 있으면 각 항목의 키/타입을 검증해
        이후 코드가 예상치 못한 값 때문에 죽지 않게 함. "엣지 컬렉션 매니저"가 만든
        collections.json도 읽을 수 있음(이 앱이 쓰지 않는 여분의 키는 무시함)."""
        data = self._read_json(
            self.collections_file,
            lambda d: isinstance(d, dict) and isinstance(d.get("collections"), list))
        if data is NO_DATA:
            return {"collections": []}
        # 항목/폴더 id가 겹치면 새로 만듦 (직접 편집한 파일 대비)
        seen_parents, seen_items = set(), set()
        cleaned = []
        for col in data["collections"]:
            if not isinstance(col, dict):
                continue
            raw_items = col.get("items")
            items = []
            for it in (raw_items if isinstance(raw_items, list) else []):
                if not isinstance(it, dict):
                    continue
                items.append({
                    "id": unique_id(it.get("id"), seen_items),
                    "title": str(it.get("title", "")),
                    "url": str(it.get("url", "")),
                    "memo": str(it.get("memo", "")),
                    "added": str(it.get("added", "")),
                })
            cleaned.append({
                "id": unique_id(col.get("id"), seen_parents),
                "name": str(col.get("name", "이름 없음")),
                "created": str(col.get("created", "")),
                "items": items,
            })
        return {"collections": cleaned}

    def save_collections(self, data):
        try:
            self._atomic_write_json(self.collections_file, data)
            return True
        except Exception as e:
            print(f"❌ 컬렉션 저장 실패: {e}")
            return False

    def load_checklists(self):
        """checklists.json 로드: {"folders": [{"id","name","created",
        "items":[{"id","content","checked","added"}]}]} 형태. load_collections와
        같은 방식으로 파일이 없거나 손상되었으면 빈 폴더 목록을 반환하고, 있으면
        각 항목의 키/타입을 검증해 이후 코드가 예상치 못한 값 때문에 죽지 않게 함"""
        data = self._read_json(
            self.checklists_file,
            lambda d: isinstance(d, dict) and isinstance(d.get("folders"), list))
        if data is NO_DATA:
            return {"folders": []}
        # 항목/폴더 id가 겹치면 새로 만듦 (직접 편집한 파일 대비)
        seen_parents, seen_items = set(), set()
        cleaned = []
        for folder in data["folders"]:
            if not isinstance(folder, dict):
                continue
            raw_items = folder.get("items")
            items = []
            for it in (raw_items if isinstance(raw_items, list) else []):
                if not isinstance(it, dict):
                    continue
                items.append({
                    "id": unique_id(it.get("id"), seen_items),
                    "content": str(it.get("content", "")),
                    "checked": bool(it.get("checked", False)),
                    "added": str(it.get("added", "")),
                })
            cleaned.append({
                "id": unique_id(folder.get("id"), seen_parents),
                "name": str(folder.get("name", "이름 없음")),
                "created": str(folder.get("created", "")),
                "items": items,
            })
        return {"folders": cleaned}

    def save_checklists(self, data):
        try:
            self._atomic_write_json(self.checklists_file, data)
            return True
        except Exception as e:
            print(f"❌ 체크리스트 저장 실패: {e}")
            return False


class SettingsManager:
    """글꼴/복사단축키/테마/빠른입력 설정의 살아있는 상태와, 그 설정들을
    편집하는 팝업창들을 담당. 실제 파일 입출력은 app.store(MemoStore)에 위임함."""

    def __init__(self, app):
        self.app = app
        self.settings = app.store.load_settings()
        self.quick_inputs = app.store.load_quick_inputs()
        self.theme_mode = self.settings.get("theme_mode", "light")
        self.content_font = (self.settings.get("font_family"), self.settings.get("font_size"))
        self.copy_shortcut = self.settings.get("copy_shortcut")

    def save(self):
        """현재 창 크기/위치를 포함해 settings.ini 전체를 저장"""
        self.settings["window_geometry"] = self.app.root.geometry()
        return self.app.store.save_settings(self.settings)

    def save_quick_inputs(self):
        return self.app.store.save_quick_inputs(self.quick_inputs)

    def bind_copy_shortcut(self):
        """현재 설정된 복사 단축키를 바인딩"""
        shortcut_map = {
            "Ctrl+Shift+C": "<Control-Shift-C>",
            "Ctrl+Alt+C": "<Control-Alt-c>",
            "Alt+Shift+C": "<Alt-Shift-C>"
        }
        binding = shortcut_map.get(self.copy_shortcut, "<Control-Shift-C>")
        self.app.root.bind(binding, self.app.copy_to_clipboard)

    def unbind_copy_shortcut(self):
        """모든 복사 단축키 바인딩 제거"""
        for seq in ("<Control-Shift-C>", "<Control-Alt-c>", "<Alt-Shift-C>"):
            try:
                self.app.root.unbind(seq)
            except Exception:
                pass

    def open_font_settings(self):
        settings_win = Toplevel(self.app.root)
        settings_win.title("글꼴 설정")
        settings_win.geometry("350x150")
        settings_win.resizable(False, False)
        settings_win.transient(self.app.root)
        settings_win.grab_set()
        settings_win.focus_force()
        # cancel_action은 아래에서 정의되지만, 람다는 Esc를 누를 때 이름을 찾으므로 미리 바인딩해도 됨
        settings_win.bind("<Escape>", lambda e: cancel_action())

        ttk.Label(settings_win, text="글꼴:", font=UI_FONT).grid(row=0, column=0, padx=10, pady=10, sticky="w")
        font_families = sorted(font.families())
        font_var = tk.StringVar(value=self.content_font[0])
        font_combo = ttk.Combobox(settings_win, textvariable=font_var, values=font_families, state="readonly")
        font_combo.grid(row=0, column=1, padx=10, pady=10, sticky="ew")
        font_combo.focus_set()

        ttk.Label(settings_win, text="크기:", font=UI_FONT).grid(row=1, column=0, padx=10, pady=10, sticky="w")
        size_var = tk.StringVar(value=str(self.content_font[1]))
        size_spinbox = ttk.Spinbox(settings_win, from_=FONT_SIZE_MIN, to=FONT_SIZE_MAX, textvariable=size_var, width=5)
        size_spinbox.grid(row=1, column=1, padx=10, pady=10, sticky="w")

        def apply_and_save():
            """입력값을 검사해 적용·저장함. 입력이 올바르지 않으면 안내만 하고 False를 반환함
            (스핀박스는 직접 입력한 값의 범위/숫자 여부를 검사하지 않으므로 여기서 확인)"""
            new_font_family = font_var.get()
            try:
                new_font_size = int(size_var.get())
            except ValueError:
                new_font_size = None
            if new_font_size is None or not (FONT_SIZE_MIN <= new_font_size <= FONT_SIZE_MAX):
                messagebox.showerror(
                    "오류", f"글자 크기는 {FONT_SIZE_MIN}~{FONT_SIZE_MAX} 사이의 정수로 입력하세요.",
                    parent=settings_win)
                size_spinbox.focus_set()
                return False
            self.content_font = (new_font_family, new_font_size)
            for tab in self.app.tabs:
                tab.set_content_font(self.content_font)
            self.settings["font_family"] = new_font_family
            self.settings["font_size"] = new_font_size
            self.save()
            return True

        def save_action():
            if apply_and_save():
                settings_win.destroy()

        def cancel_action():
            settings_win.destroy()

        button_frame = ttk.Frame(settings_win)
        button_frame.grid(row=2, column=0, columnspan=2, pady=10)
        save_button = ttk.Button(button_frame, text="저장", command=save_action, width=10)
        save_button.pack(side=tk.LEFT, padx=5)
        cancel_button = ttk.Button(button_frame, text="취소", command=cancel_action, width=10)
        cancel_button.pack(side=tk.LEFT, padx=5)

    def open_shortcut_settings(self):
        settings_win = Toplevel(self.app.root)
        settings_win.title("단축키 설정")
        settings_win.geometry("350x150")
        settings_win.resizable(False, False)
        settings_win.transient(self.app.root)
        settings_win.grab_set()
        settings_win.focus_force()
        settings_win.bind("<Escape>", lambda e: cancel_action())

        ttk.Label(settings_win, text="클립보드 복사:", font=UI_FONT).grid(row=0, column=0, padx=10, pady=10, sticky="w")

        shortcut_options = ["Ctrl+Shift+C", "Ctrl+Alt+C", "Alt+Shift+C"]
        shortcut_var = tk.StringVar(value=self.copy_shortcut)
        shortcut_combo = ttk.Combobox(settings_win, textvariable=shortcut_var, values=shortcut_options, state="readonly", width=20)
        shortcut_combo.grid(row=0, column=1, padx=10, pady=10, sticky="ew")
        shortcut_combo.focus_set()

        def apply_and_save():
            new_shortcut = shortcut_var.get()
            self.unbind_copy_shortcut()
            self.copy_shortcut = new_shortcut
            self.settings["copy_shortcut"] = new_shortcut
            self.bind_copy_shortcut()
            self.save()

        def save_action():
            apply_and_save()
            settings_win.destroy()

        def cancel_action():
            settings_win.destroy()

        button_frame = ttk.Frame(settings_win)
        button_frame.grid(row=2, column=0, columnspan=2, pady=10)
        save_button = ttk.Button(button_frame, text="저장", command=save_action, width=10)
        save_button.pack(side=tk.LEFT, padx=5)
        cancel_button = ttk.Button(button_frame, text="취소", command=cancel_action, width=10)
        cancel_button.pack(side=tk.LEFT, padx=5)

    def open_theme_settings(self):
        settings_win = Toplevel(self.app.root)
        settings_win.title("테마 설정")
        settings_win.geometry("300x140")
        settings_win.resizable(False, False)
        settings_win.transient(self.app.root)
        settings_win.grab_set()
        settings_win.focus_force()
        settings_win.bind("<Escape>", lambda e: cancel_action())

        ttk.Label(settings_win, text="테마:", font=UI_FONT).grid(row=0, column=0, padx=10, pady=10, sticky="w")

        theme_labels = {"light": "밝게 (Light)", "dark": "어둡게 (Dark)"}
        label_to_mode = {v: k for k, v in theme_labels.items()}
        theme_var = tk.StringVar(value=theme_labels.get(self.theme_mode, theme_labels["light"]))
        theme_combo = ttk.Combobox(
            settings_win, textvariable=theme_var,
            values=list(theme_labels.values()), state="readonly", width=15
        )
        theme_combo.grid(row=0, column=1, padx=10, pady=10, sticky="ew")
        theme_combo.focus_set()

        def apply_and_save():
            new_mode = label_to_mode.get(theme_var.get(), "light")
            self.theme_mode = new_mode
            self.settings["theme_mode"] = new_mode
            if sv_ttk:
                sv_ttk.set_theme(new_mode, self.app.root)
            apply_titlebar_theme(self.app.root, new_mode == "dark")
            self.app.apply_theme_colors()
            self.save()

        def save_action():
            apply_and_save()
            settings_win.destroy()

        def cancel_action():
            settings_win.destroy()

        button_frame = ttk.Frame(settings_win)
        button_frame.grid(row=2, column=0, columnspan=2, pady=10)
        save_button = ttk.Button(button_frame, text="저장", command=save_action, width=10)
        save_button.pack(side=tk.LEFT, padx=5)
        cancel_button = ttk.Button(button_frame, text="취소", command=cancel_action, width=10)
        cancel_button.pack(side=tk.LEFT, padx=5)

    def open_quick_input_settings(self):
        """Alt+1~Alt+0 빠른 입력 문구를 설정하는 팝업창"""
        settings_win = Toplevel(self.app.root)
        settings_win.title("빠른 입력 설정")
        settings_win.resizable(False, False)
        settings_win.transient(self.app.root)
        settings_win.grab_set()
        settings_win.focus_force()
        settings_win.bind("<Escape>", lambda e: cancel_action())

        info_label = ttk.Label(
            settings_win,
            text="Alt+숫자 키를 눌렀을 때 삽입할 문구를 입력하세요.",
            font=UI_FONT,
        )
        info_label.grid(row=0, column=0, columnspan=2, padx=10, pady=(10, 5), sticky="w")

        entries = {}
        for row, key in enumerate(QUICK_INPUT_KEYS, start=1):
            ttk.Label(settings_win, text=f"Alt+{key} :", font=UI_FONT).grid(
                row=row, column=0, padx=(10, 5), pady=4, sticky="w"
            )
            entry = ttk.Entry(settings_win, width=40, font=UI_FONT)
            entry.insert(0, self.quick_inputs.get(key, ""))
            entry.grid(row=row, column=1, padx=(0, 10), pady=4, sticky="ew")
            entries[key] = entry

        entries[QUICK_INPUT_KEYS[0]].focus_set()

        def apply_and_save():
            for key, entry in entries.items():
                self.quick_inputs[key] = entry.get()
            self.save_quick_inputs()

        def apply_action():
            apply_and_save()
            settings_win.destroy()

        def cancel_action():
            settings_win.destroy()

        button_frame = ttk.Frame(settings_win)
        button_frame.grid(row=len(QUICK_INPUT_KEYS) + 1, column=0, columnspan=2, pady=10)
        apply_button = ttk.Button(button_frame, text="적용", command=apply_action, width=10)
        apply_button.pack(side=tk.LEFT, padx=5)
        cancel_button = ttk.Button(button_frame, text="취소", command=cancel_action, width=10)
        cancel_button.pack(side=tk.LEFT, padx=5)


class GeneralMemoTab:
    """"일반메모" 탭: 왼쪽 메모 목록(추가/제거/순서변경/드래그) + 오른쪽 제목/내용 편집."""

    def __init__(self, parent, app):
        self.app = app
        self.memos = app.store.load_memos()
        self.current_index = -1
        self.drag_start_index = None

        self.main_pane = ttk.PanedWindow(parent, orient=tk.HORIZONTAL)
        self.main_pane.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        main_pane = self.main_pane

        # 왼쪽 패널: 메모 리스트
        left_panel = ttk.Frame(main_pane)
        main_pane.add(left_panel, weight=0)

        list_frame = ttk.Frame(left_panel)
        list_frame.pack(fill=tk.BOTH, expand=True)

        self.listbox = tk.Listbox(list_frame, exportselection=False, font=UI_FONT)
        self.listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.listbox.bind("<<ListboxSelect>>", self.on_memo_select)
        # 목록 단축키는 목록이 화면에 보일 때만 동작함 (bind_when_visible 참고)
        bind_when_visible(self.listbox, "<Delete>", lambda event: self.remove_memo())
        bind_when_visible(self.listbox, "<Home>", self.on_home_key)
        bind_when_visible(self.listbox, "<End>", self.on_end_key)

        # 드래그 앤 드롭 이벤트 바인딩
        self.listbox.bind("<ButtonPress-1>", self.on_drag_start)
        self.listbox.bind("<B1-Motion>", self.on_drag_motion)
        self.listbox.bind("<ButtonRelease-1>", self.on_drag_drop)

        scrollbar = ttk.Scrollbar(list_frame, orient="vertical", command=self.listbox.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.listbox.config(yscrollcommand=scrollbar.set)

        self.update_listbox()

        # 버튼 프레임
        button_frame = ttk.Frame(left_panel)
        button_frame.pack(fill=tk.X, pady=5)

        add_button = ttk.Button(button_frame, text="추가", command=self.add_memo)
        add_button.pack(side=tk.LEFT, expand=True, fill=tk.X)
        remove_button = ttk.Button(button_frame, text="제거", command=self.remove_memo)
        remove_button.pack(side=tk.LEFT, expand=True, fill=tk.X)
        up_button = ttk.Button(button_frame, text="▲", command=self.move_memo_up)
        up_button.pack(side=tk.LEFT, expand=True, fill=tk.X)
        down_button = ttk.Button(button_frame, text="▼", command=self.move_memo_down)
        down_button.pack(side=tk.LEFT, expand=True, fill=tk.X)

        # 오른쪽 패널: 제목 + 내용
        right_panel = ttk.Frame(main_pane)
        main_pane.add(right_panel, weight=1)

        title_label = ttk.Label(right_panel, text="메모 제목", font=UI_FONT)
        title_label.pack(anchor="w")
        self.title_entry = ttk.Entry(right_panel, font=UI_FONT)
        self.title_entry.pack(fill=tk.X, pady=(0, 10))
        self.title_entry.bind("<KeyRelease>", self.update_memo_realtime)
        self.title_entry.bind("<Control-t>", self.app.focus_on_title)

        content_label = ttk.Label(right_panel, text="메모 내용", font=UI_FONT)
        content_label.pack(anchor="w")
        # height=1: 지정하지 않으면 Text 기본 높이(24줄)가 자연 요구 크기가 되어, 창이 작을 때
        # 아래 [복사] 버튼 등 형제 위젯이 창 밖으로 밀려남. 실제 크기는 fill=BOTH+expand가 결정함
        self.content_text = tk.Text(right_panel, font=app.settings_mgr.content_font, padx=10, pady=8, height=1,
                                    **TEXT_UNDO_OPTIONS)
        bind_redo_shortcuts(self.content_text)
        self.content_text.pack(fill=tk.BOTH, expand=True)
        self.content_text.bind("<KeyRelease>", lambda event: self.update_memo_realtime(event, update_list=False))
        self.content_text.bind("<ButtonRelease-1>", self.app.update_status_bar)
        self.content_text.bind("<Control-t>", self.app.focus_on_title)

        # 복사 버튼과 복사 완료 메시지를 위한 프레임
        copy_frame = ttk.Frame(right_panel)
        copy_frame.pack(anchor="e", pady=5)

        self.copy_status_label = ttk.Label(copy_frame, text="", font=("맑은 고딕", 11, "bold"))
        self.copy_status_label.pack(side=tk.LEFT, padx=(0, 10))

        self.copy_button = ttk.Button(copy_frame, text="클립보드로 복사", command=self.app.copy_to_clipboard)
        self.copy_button.pack(side=tk.LEFT)

    # ---- MemoApp이 공통으로 호출하는 인터페이스 ----

    def set_content_font(self, font_tuple):
        self.content_text.config(font=font_tuple)

    def apply_theme_colors(self, colors):
        self.listbox.config(
            bg=colors["bg"], fg=colors["fg"],
            selectbackground=colors["list_select_bg"],
            selectforeground=colors["list_select_fg"],
            relief=tk.FLAT, borderwidth=0,
            highlightthickness=1,
            highlightbackground=colors["border"],
            highlightcolor=colors["accent"],
        )
        enabled = self.content_text.cget("state") == tk.NORMAL
        self.content_text.config(
            bg=colors["bg"] if enabled else colors["disabled_bg"],
            fg=colors["fg"],
            insertbackground=colors["insert_bg"],
            selectbackground=colors["text_select_bg"],
            selectforeground=colors["text_select_fg"],
            relief=tk.FLAT, borderwidth=0,
            highlightthickness=1,
            highlightbackground=colors["border"],
            highlightcolor=colors["accent"],
        )

    def get_status_text(self):
        memo_count = len(self.memos)
        status_text = f"총 {memo_count}개의 메모"
        if self.current_index != -1 and self.content_text.cget('state') == tk.NORMAL:
            cursor_pos = self.content_text.index(tk.INSERT)
            row, column = cursor_pos.split('.')
            row = int(row)
            column = int(column) + 1
            content = self.content_text.get("1.0", tk.END).strip()
            char_count = len(content)
            status_text += f" / 커서 위치: 줄 {row}, 열 {column} / 글자 수: {char_count}자"
        return status_text

    def get_copy_target(self):
        if self.current_index == -1:
            return None
        return (self.content_text, self.copy_status_label)

    def restore_layout(self):
        """창 위치/크기 복원 직후 호출: 좌측 리스트 패널의 초기 폭을 지정.
        (ttk.PanedWindow는 add()에서 width/minsize를 못 받아 sashpos로 대신 처리)"""
        try:
            self.app.root.update_idletasks()
            self.main_pane.sashpos(0, 250)
        except Exception:
            pass
        self.main_pane.bind("<ButtonRelease-1>", lambda e: self.enforce_min_sash(e, self.main_pane, 200))

    def enforce_min_sash(self, event=None, pane=None, min_width=200):
        """왼쪽 리스트 패널이 너무 좁아지지 않도록 최소 폭을 보정."""
        pane = pane if pane is not None else self.main_pane
        try:
            if pane.sashpos(0) < min_width:
                pane.sashpos(0, min_width)
        except Exception:
            pass

    # ---- 탭 전용/공통 단축키 인터페이스 (MemoApp이 활성 탭에 위임함) ----

    def on_ctrl_n(self, event=None):
        self.add_memo()
        return "break"

    def on_ctrl_d(self, event=None):
        """Ctrl+D: 제목/내용 편집창에 포커스가 있을 때만 선택된 메모를 삭제.
        (메모 목록 자체에 포커스가 있을 때는 이미 Delete 키가 그 역할을 함)"""
        focused = self.app.root.focus_get()
        if focused is self.title_entry or focused is self.content_text:
            self.remove_memo()
            return "break"
        return None

    def focus_content(self, event=None):
        if str(self.content_text.cget("state")) == tk.NORMAL:
            self.content_text.focus_set()
        return "break"

    def focus_primary(self, event=None):
        # ttk.Entry의 cget('state')는 일반 str이 아닌 Tcl 객체를 반환하므로 str()로 변환 후 비교해야 함
        if str(self.title_entry.cget('state')) == tk.NORMAL:
            self.title_entry.focus_set()
            self.title_entry.select_range(0, tk.END)
        return "break"

    def focus_list(self, event=None):
        self.focus_on_listbox()
        return "break"

    def on_page_up(self, event=None):
        if self._is_listbox_focused():
            self.move_memo_up()

    def on_page_down(self, event=None):
        if self._is_listbox_focused():
            self.move_memo_down()

    def insert_text_at_widget(self, widget, text):
        """Alt+T(날짜/시간)·Alt+숫자(빠른 입력)의 삽입 대상인지 확인하고, 맞으면
        삽입 후 True를 반환함. (MemoApp._insert_text_at_focus가 모든 탭에 순서대로
        물어보므로, 이 탭의 위젯이 아니면 False를 반환해 다음 탭에게 넘김)"""
        if widget is self.title_entry:
            try:
                self.title_entry.delete("sel.first", "sel.last")
            except tk.TclError:
                pass
            self.title_entry.insert(tk.INSERT, text)
            self.update_memo_realtime(update_list=True)
            return True
        if widget is self.content_text:
            insert_text_as_one_undo_step(self.content_text, text)
            self.update_memo_realtime(update_list=False)
            return True
        return False

    # ---- 메모 목록/편집 ----

    def toggle_right_panel(self, enabled):
        state = tk.NORMAL if enabled else tk.DISABLED
        colors = THEME_COLORS.get(self.app.settings_mgr.theme_mode, THEME_COLORS["light"])
        self.title_entry.config(state=state)
        self.content_text.config(state=state, bg=colors["bg"] if enabled else colors["disabled_bg"])
        self.copy_button.config(state=state)
        self.app.update_status_bar()

    def update_listbox(self, preserve_scroll=False, top_adjust=0):
        """
        리스트박스를 다시 그림. 다시 그리면 스크롤이 맨 위로 초기화되므로 필요하면 보던 위치를 유지함.

        Args:
            preserve_scroll: True이면 다시 그리기 전에 맨 위에 보이던 행 번호를 기억했다가
                그 위치로 되돌림. (스크롤 비율은 행 수가 바뀌면 어긋나므로 행 번호 기준)
            top_adjust: 보던 위치보다 앞쪽 행이 추가/삭제되어 행 번호가 밀린 만큼의 보정값
                (예: 화면 위쪽에 있던 행을 삭제했다면 -1)
        """
        top = self.listbox.nearest(0) if (preserve_scroll and self.listbox.size()) else None

        self.listbox.delete(0, tk.END)
        for memo in self.memos:
            self.listbox.insert(tk.END, memo["title"])

        if top is not None and self.listbox.size():
            self.listbox.yview(max(0, min(top + top_adjust, self.listbox.size() - 1)))

        self.app.update_status_bar()

    def on_memo_select(self, event):
        selected_indices = self.listbox.curselection()
        if not selected_indices:
            return
        self.current_index = selected_indices[0]
        memo = self.memos[self.current_index]
        self.toggle_right_panel(True)
        self.title_entry.delete(0, tk.END)
        self.title_entry.insert(0, memo["title"])
        set_text_content(self.content_text, memo["content"])
        self.app.update_status_bar()

    def add_memo(self):
        new_memo = {"title": "새 메모", "content": ""}
        insert_pos = self.current_index + 1 if self.current_index != -1 else len(self.memos)
        self.memos.insert(insert_pos, new_memo)
        self.update_listbox(preserve_scroll=True)
        self.listbox.selection_clear(0, tk.END)
        self.listbox.selection_set(insert_pos)
        self.listbox.activate(insert_pos)
        self.listbox.see(insert_pos)  # 새 메모가 화면 밖(예: 맨 끝에 추가)이면 보이는 위치로 이동
        self.on_memo_select(None)
        self.app.save_memos()

    def remove_memo(self):
        if self.current_index == -1:
            messagebox.showwarning("경고", "삭제할 메모를 선택하세요.")
            return
        if messagebox.askyesno("확인", "선택한 메모를 제거하시겠습니까?"):
            removed_index = self.current_index
            top_before = self.listbox.nearest(0)
            del self.memos[removed_index]
            self.current_index = -1
            self.title_entry.delete(0, tk.END)
            set_text_content(self.content_text)
            self.toggle_right_panel(False)
            # 화면 위쪽(보이는 영역보다 앞)의 행을 지웠다면 아래 행들이 한 칸씩 올라오므로
            # 보던 첫 행이 그대로 맨 위에 오도록 한 칸 보정함
            self.update_listbox(preserve_scroll=True,
                                top_adjust=-1 if removed_index < top_before else 0)
            if self.memos:
                # 다시 그리면 활성(active) 항목이 0번으로 초기화되어 이어서 ↑↓를 누르면
                # 목록 맨 위 근처로 튀므로 삭제한 자리로 되돌림 (선택은 하지 않음)
                self.listbox.activate(min(removed_index, len(self.memos) - 1))
            self.app.save_memos()

    def move_memo_up(self):
        if self.current_index > 0:
            self.memos.insert(self.current_index - 1, self.memos.pop(self.current_index))
            self.current_index -= 1
            self.update_listbox_selection()

    def move_memo_down(self):
        if 0 <= self.current_index < len(self.memos) - 1:
            self.memos.insert(self.current_index + 1, self.memos.pop(self.current_index))
            self.current_index += 1
            self.update_listbox_selection()

    def _is_listbox_focused(self):
        """PageUp/PageDown 순서변경 단축키를 리스트박스에 포커스가 있을 때만 허용하기 위한
        확인. Text/Entry의 기본 Prior/Next 바인딩은 break를 호출하지 않아 이벤트가 root까지
        전파되므로, 이 확인이 없으면 메모 내용을 스크롤하려고 PageUp/PageDown을 눌러도
        (다른 탭에서도) 메모 순서가 바뀜."""
        return self.app.root.focus_get() is self.listbox

    def on_home_key(self, event=None):
        if not self.memos:
            return "break"
        self.listbox.focus_set()
        self.listbox.selection_clear(0, tk.END)
        self.listbox.selection_set(0)
        self.on_memo_select(None)
        self.listbox.activate(0)
        self.listbox.see(0)
        return "break"

    def on_end_key(self, event=None):
        if not self.memos:
            return "break"
        last_index = len(self.memos) - 1
        self.listbox.focus_set()
        self.listbox.selection_clear(0, tk.END)
        self.listbox.selection_set(last_index)
        self.on_memo_select(None)
        self.listbox.activate(last_index)
        self.listbox.see(last_index)
        return "break"

    def focus_on_listbox(self):
        self.listbox.focus_set()
        if self.current_index != -1:
            self.listbox.selection_set(self.current_index)
            self.listbox.activate(self.current_index)

    def update_listbox_selection(self):
        """메모 위치 변경 시 스크롤 위치를 유지하면서 업데이트"""
        self.update_listbox(preserve_scroll=True)
        self.listbox.selection_set(self.current_index)
        self.listbox.activate(self.current_index)
        self.listbox.see(self.current_index)
        self.on_memo_select(None)
        self.app.save_memos()

    def update_memo_realtime(self, event=None, update_list=True):
        """실시간으로 메모를 업데이트

        Args:
            update_list: True면 리스트박스에 보이는 제목도 함께 갱신한다.
                title_entry 입력처럼 화면에 보이는 제목이 바뀌는 경우에만 True로 호출하고,
                content_text 입력처럼 제목은 그대로인 경우 False로 호출하면 매 키 입력마다
                리스트박스 전체를 delete+재삽입하지 않아도 되어 더 가볍다.
        """
        if self.current_index == -1:
            return

        title = self.title_entry.get()
        # "end-1c": Text가 항상 끝에 붙이는 개행 한 글자만 제외함. .strip()은 사용자가 넣은
        # 끝줄 공백/빈 줄까지 지우므로 쓰지 않고 원본 그대로 저장함
        content = self.content_text.get("1.0", "end-1c")
        self.memos[self.current_index] = {"title": title, "content": content}

        if update_list:
            # 전체 delete(0, END)+재삽입 대신, 바뀐 항목 하나만 갱신
            # (다른 항목은 그대로라 스크롤 위치도 자연히 유지됨)
            self.listbox.delete(self.current_index)
            self.listbox.insert(self.current_index, title)
            self.listbox.selection_set(self.current_index)
            # delete+insert 때문에 활성(active) 항목이 한 칸 뒤로 밀리면, 이후 목록에서
            # ↓를 눌렀을 때 한 행을 건너뛰므로 편집 중인 행으로 되돌림
            self.listbox.activate(self.current_index)

        self.app._debounced_save("memos", self.app.save_memos)
        self.app.update_status_bar()

    def on_drag_start(self, event):
        """드래그 시작: 시작 인덱스 저장"""
        self.drag_start_index = self.listbox.nearest(event.y)
        return

    def on_drag_motion(self, event):
        """드래그 중: 현재 마우스 위치를 활성(active) 표시로만 안내함.
        Listbox의 기본 클래스 바인딩은 <B1-Motion>에서 지나가는 항목을 스스로 선택하고
        <<ListboxSelect>>를 발생시켜 편집창이 바뀌므로, 반드시 "break"를 반환해 기본 동작을
        막아야 함."""
        if self.drag_start_index is None:
            return

        current_index = self.listbox.nearest(event.y)

        if 0 <= current_index < len(self.memos):
            self.listbox.activate(current_index)

        return "break"

    def on_drag_drop(self, event):
        """드롭: 메모 순서 변경"""
        if self.drag_start_index is None:
            return

        drop_index = self.listbox.nearest(event.y)

        if not (0 <= drop_index < len(self.memos)):
            self.drag_start_index = None
            return

        if self.drag_start_index == drop_index:
            self.drag_start_index = None
            return

        memo = self.memos.pop(self.drag_start_index)
        self.memos.insert(drop_index, memo)

        self.current_index = drop_index

        self.update_listbox_selection()

        self.drag_start_index = None

    # ---- 가져오기/내보내기/백업 훅 ----
    # 파일 선택/확인창/형식별 저장 흐름은 MemoApp이 모든 탭에 공통으로 처리하고, 탭은 자기
    # 데이터에 고유한 부분(검증, 화면 반영, TXT/XLSX 모양)만 아래 훅으로 제공함 (파일 위
    # "앱 구조 안내" 참고)

    transfer_label = "일반메모"
    transfer_filename = "memos.json"

    def transfer_parse(self, raw):
        """가져온 JSON을 검증하고 정규화한 메모 리스트를 반환 (구조가 잘못되면 TypeError/ValueError).
        키 존재만 보면 title이 숫자거나 content가 객체인 경우도 통과하므로 값의 타입까지 확인함.
        memos.json 로드(load_memos)와 달리 가져오기는 사용자가 확인하고 실행하는 동작이라
        조용히 보정하지 않고 오류로 알림."""
        if not isinstance(raw, list):
            raise TypeError("데이터가 리스트 형식이 아닙니다.")
        cleaned = []
        for m in raw:
            if not isinstance(m, dict):
                raise ValueError("메모 항목이 딕셔너리가 아닙니다.")
            if not isinstance(m.get("title"), str):
                raise ValueError("메모 제목은 문자열이어야 합니다.")
            if not isinstance(m.get("content"), str):
                raise ValueError("메모 내용은 문자열이어야 합니다.")
            cleaned.append({"title": m["title"], "content": m["content"]})
        return cleaned

    def transfer_summary(self, data):
        return f"메모 {len(data)}개"

    def transfer_apply(self, data):
        self.memos = data
        ok = self.app.save_memos()
        self.current_index = -1
        self.title_entry.delete(0, tk.END)
        set_text_content(self.content_text)
        self.toggle_right_panel(False)
        self.update_listbox()
        return ok

    def transfer_export_json(self):
        return self.memos

    def transfer_export_txt(self):
        return "".join(
            f"제목: {memo['title']}\n" + "-" * 20 + f"\n{memo['content']}\n\n" + "=" * 20 + "\n\n"
            for memo in self.memos)

    def transfer_export_xlsx(self):
        return "메모", ["제목", "내용"], [[memo["title"], memo["content"]] for memo in self.memos]

class CalendarMemoTab:
    """"달력메모" 탭: 왼쪽 달력([월별보기]/[1년전체보기]/[목록보기]) + 오른쪽 날짜별 메모 내용."""

    def __init__(self, parent, app):
        self.app = app
        self.calendar_memos = app.store.load_calendar_memos()
        self.holidays = app.store.load_holidays()  # {"YYYY-MM-DD": "공휴일 이름"} - 참고용
        self._holiday_tooltip = None  # 공휴일 이름 풍선말 Toplevel (없으면 None)
        self.weekday_label_widgets = []  # (라벨위젯, "sun"|"sat"|"normal") - 테마 갱신용

        now = datetime.now()
        self.cal_year, self.cal_month = now.year, now.month
        self.cal_year_year = now.year
        self.selected_date = self._today_str()

        cal_container = ttk.Frame(parent)
        cal_container.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        self.calendar_pane = cal_container

        # ---- 왼쪽: 달력 (고정 폭: 크기조절 막대로 바꿀 수 없도록 PanedWindow 대신 Frame 사용) ----
        cal_left = ttk.Frame(cal_container, width=CAL_LEFT_WIDTH)
        cal_left.pack(side=tk.LEFT, fill=tk.Y)
        cal_left.pack_propagate(False)

        ttk.Separator(cal_container, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=8)

        self.cal_view_notebook = ttk.Notebook(cal_left)

        # 기본 ttk 버튼은 좌우 패딩이 넓어 고정폭 안에 여러 개를 놓으면 잘리므로, 이 좌측
        # 영역(cal_left)의 버튼들(아래 공용 4버튼과 월별보기의 이전/오늘/다음)은 패딩을 줄인
        # 전용 스타일을 공유함
        nav_btn_style = ttk.Style()
        nav_btn_style.configure("CalNav.TButton", padding=(2, 4), width=1)

        # [추가]/[제거]/[◀이전]/[다음▶] 버튼 - 달력 영역(cal_left) 맨 아래, 상태표시줄 바로 위.
        # side=BOTTOM으로 먼저 배치해야 아래에서 expand=True로 채워지는 노트북이 이 영역을
        # 침범하지 않음(pack은 호출 순서대로 공간을 배정함). [월별보기]/[1년전체보기]/
        # [목록보기] 중 어느 서브탭에 있든 항상 같은 자리에서 같은 동작을 함. 전용 스타일
        # (CalNav.TButton)로 패딩을 줄여 고정폭(CAL_LEFT_WIDTH) 안에 4개가 모두 보임
        cal_nav_buttons = ttk.Frame(cal_left)
        cal_nav_buttons.pack(side=tk.BOTTOM, fill=tk.X, pady=(6, 0))
        add_memo_btn = ttk.Button(cal_nav_buttons, text="추가", style="CalNav.TButton",
                                   command=self._open_add_memo_dialog)
        add_memo_btn.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=(0, 2))
        # 선택된 날짜에 이미 내용이 있을 때만 활성화 (초기 상태 - 아래 date_content_text가
        # 아직 만들어지기 전이므로 위젯이 아닌 calendar_memos 딕셔너리로 직접 확인)
        initial_has_content = bool(self.calendar_memos.get(self.selected_date, "").strip())
        self.remove_date_memo_button = ttk.Button(
            cal_nav_buttons, text="제거", style="CalNav.TButton", command=self.remove_date_memo,
            state=(tk.NORMAL if initial_has_content else tk.DISABLED))
        self.remove_date_memo_button.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=(2, 2))
        self.prev_memo_button = ttk.Button(cal_nav_buttons, text="◀ 이전", style="CalNav.TButton",
                                            command=lambda: self.go_to_adjacent_memo_date(-1))
        self.prev_memo_button.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=(2, 2))
        self.next_memo_button = ttk.Button(cal_nav_buttons, text="다음 ▶", style="CalNav.TButton",
                                            command=lambda: self.go_to_adjacent_memo_date(1))
        self.next_memo_button.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=(2, 0))

        self.cal_view_notebook.pack(fill=tk.BOTH, expand=True)
        self.cal_view_notebook.bind("<<NotebookTabChanged>>", self._on_cal_view_tab_changed)
        # cal_view_notebook은 ttk.Notebook이라 Ctrl+Tab/Ctrl+Shift+Tab에 대한 자체 기본
        # 바인딩(자신의 서브탭끼리 전환)을 가짐. 이 위젯에 포커스가 있으면(탭 헤더를 클릭하거나
        # Alt+M/Y/L로 전환한 직후 등) 그 기본 동작이 root 레벨 바인딩보다 먼저 실행되어 최상단
        # 탭 대신 서브탭끼리만 전환됨. 인스턴스에 같은 키를 직접 바인딩하고 "break"로 가로채면
        # 클래스 기본 동작보다 먼저 처리됨
        self.cal_view_notebook.bind("<Control-Tab>", lambda e: self.app._cycle_top_tab(1))
        self.cal_view_notebook.bind("<Control-Shift-Tab>", lambda e: self.app._cycle_top_tab(-1))

        month_tab = ttk.Frame(self.cal_view_notebook)
        year_tab = ttk.Frame(self.cal_view_notebook)
        list_tab = ttk.Frame(self.cal_view_notebook)
        self.cal_view_notebook.add(month_tab, text="월별보기")
        self.cal_view_notebook.add(year_tab, text="1년전체보기")
        self.cal_view_notebook.add(list_tab, text="목록보기")

        # -- 월별보기 --
        self.month_year_var = tk.StringVar(value=str(self.cal_year))
        self.month_month_var = tk.StringVar(value=f"{self.cal_month}월")

        # 1행: 연도/월 선택, 2행: 이전/오늘/다음 (한 줄에 다 넣으면 폰트에 따라 "오늘" 버튼이
        # 고정 폭 밖으로 밀려날 수 있어 두 줄로 나눔 - 달력 영역 너비는 그대로 유지)
        m_nav = ttk.Frame(month_tab)
        m_nav.pack(anchor="w", padx=6, pady=(8, 2))
        m_nav.grid_columnconfigure(0, minsize=30)
        for c in range(7):
            m_nav.grid_columnconfigure(c + 1, minsize=CAL_CELL_W + 2)

        nav_controls = ttk.Frame(m_nav)
        nav_controls.grid(row=0, column=1, columnspan=7)
        year_spin = ttk.Spinbox(nav_controls, from_=CAL_MIN_YEAR, to=CAL_MAX_YEAR, textvariable=self.month_year_var,
                                 width=6, command=self._commit_month_year)
        year_spin.pack(side=tk.LEFT)
        year_spin.bind("<Return>", self._commit_month_year)
        year_spin.bind("<FocusOut>", self._commit_month_year)
        ttk.Label(nav_controls, text="년").pack(side=tk.LEFT, padx=(2, 8))

        month_combo = ttk.Combobox(nav_controls, textvariable=self.month_month_var,
                                    values=[f"{m}월" for m in range(1, 13)],
                                    state="readonly", width=5)
        month_combo.pack(side=tk.LEFT)
        month_combo.bind("<<ComboboxSelected>>", self._on_month_combo_change)

        m_nav2 = ttk.Frame(month_tab)
        m_nav2.pack(anchor="w", padx=6, pady=(0, 6))
        m_nav2.grid_columnconfigure(0, minsize=30)
        for c in range(7):
            m_nav2.grid_columnconfigure(c + 1, minsize=CAL_CELL_W + 2)

        # "CalNav.TButton" 스타일(좌우 패딩을 줄여 2칸(84px)에 정확히 맞춤)은 위
        # cal_nav_buttons 블록에서 이미 정의해뒀으므로 여기서는 재사용만 함
        ttk.Button(m_nav2, text="◀", style="CalNav.TButton",
                   command=lambda: self.go_to_month(self.cal_year, self.cal_month - 1)
                   ).grid(row=0, column=1, columnspan=2, sticky="nsew", padx=1, pady=1, ipady=4)
        ttk.Button(m_nav2, text="오늘", style="CalNav.TButton", command=self.go_to_today
                   ).grid(row=0, column=3, columnspan=3, sticky="nsew", padx=1, pady=1, ipady=4)
        ttk.Button(m_nav2, text="▶", style="CalNav.TButton",
                   command=lambda: self.go_to_month(self.cal_year, self.cal_month + 1)
                   ).grid(row=0, column=6, columnspan=2, sticky="nsew", padx=1, pady=1, ipady=4)

        m_weekday_frame = tk.Frame(month_tab)
        m_weekday_frame.pack(anchor="w", padx=6)
        m_weekday_frame.grid_columnconfigure(0, minsize=30)
        m_corner_lbl = tk.Label(m_weekday_frame, text="", width=3)
        m_corner_lbl.grid(row=0, column=0, sticky="nsew")
        self.weekday_label_widgets.append((m_corner_lbl, "normal"))
        weekday_names = ["일", "월", "화", "수", "목", "금", "토"]
        for i, wd in enumerate(weekday_names):
            m_weekday_frame.grid_columnconfigure(i + 1, minsize=CAL_CELL_W + 2)
            kind = "sun" if i == 0 else ("sat" if i == 6 else "normal")
            lbl = tk.Label(m_weekday_frame, text=wd, width=4, font=("맑은 고딕", 9, "bold"))
            lbl.grid(row=0, column=i + 1, sticky="nsew")
            self.weekday_label_widgets.append((lbl, kind))

        self.month_grid_frame = tk.Frame(month_tab)
        self.month_grid_frame.pack(anchor="w", padx=6, pady=(2, 8))

        # -- 1년전체보기 --
        self.year_year_var = tk.StringVar(value=str(self.cal_year_year))

        y_nav = ttk.Frame(year_tab)
        y_nav.pack(fill=tk.X, padx=6, pady=(8, 4))
        year_spin_y = ttk.Spinbox(y_nav, from_=CAL_MIN_YEAR, to=CAL_MAX_YEAR, textvariable=self.year_year_var,
                                   width=6, command=self._commit_year_year)
        year_spin_y.pack(side=tk.LEFT)
        year_spin_y.bind("<Return>", self._commit_year_year)
        year_spin_y.bind("<FocusOut>", self._commit_year_year)
        ttk.Label(y_nav, text="년").pack(side=tk.LEFT, padx=(2, 8))
        ttk.Button(y_nav, text="◀", width=3,
                   command=lambda: self.go_to_year(self.cal_year_year - 1)).pack(side=tk.LEFT, padx=2)
        ttk.Button(y_nav, text="▶", width=3,
                   command=lambda: self.go_to_year(self.cal_year_year + 1)).pack(side=tk.LEFT, padx=2)
        ttk.Button(y_nav, text="올해",
                   command=lambda: self.go_to_year(datetime.now().year)).pack(side=tk.LEFT, padx=(6, 0))

        y_weekday_frame = tk.Frame(year_tab)
        y_weekday_frame.pack(fill=tk.X, padx=6)
        y_weekday_frame.grid_columnconfigure(0, minsize=30)
        corner_lbl = tk.Label(y_weekday_frame, text="", width=3)
        corner_lbl.grid(row=0, column=0, sticky="nsew")
        self.weekday_label_widgets.append((corner_lbl, "normal"))
        for i, wd in enumerate(weekday_names):
            y_weekday_frame.grid_columnconfigure(i + 1, minsize=CAL_CELL_W + 2)
            kind = "sun" if i == 0 else ("sat" if i == 6 else "normal")
            lbl = tk.Label(y_weekday_frame, text=wd, width=4, font=("맑은 고딕", 9, "bold"))
            lbl.grid(row=0, column=i + 1, sticky="nsew")
            self.weekday_label_widgets.append((lbl, kind))

        y_scroll_container = ttk.Frame(year_tab)
        y_scroll_container.pack(fill=tk.BOTH, expand=True, padx=6, pady=(2, 8))
        self.year_canvas = tk.Canvas(y_scroll_container, highlightthickness=0)
        # sv_ttk 테마의 스크롤바는 매우 얇아서 눈에 잘 안 띄기 때문에, 항상 뚜렷하게 보이는
        # 기본 Tk 스크롤바를 사용해 사용자가 현재 위치를 가늠할 수 있게 함
        self.year_scrollbar = tk.Scrollbar(y_scroll_container, orient="vertical",
                                            command=self.year_canvas.yview, width=16)
        self.year_canvas.configure(yscrollcommand=self.year_scrollbar.set)
        self.year_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.year_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.year_grid_frame = tk.Frame(self.year_canvas)
        self.year_canvas.create_window((0, 0), window=self.year_grid_frame, anchor="nw")
        self.year_grid_frame.bind(
            "<Configure>",
            lambda e: self.year_canvas.configure(scrollregion=self.year_canvas.bbox("all"))
        )
        self.year_canvas.bind("<Enter>", lambda e: self.year_canvas.bind_all("<MouseWheel>", self._on_year_mousewheel))
        self.year_canvas.bind("<Leave>", lambda e: self.year_canvas.unbind_all("<MouseWheel>"))

        # -- 목록보기 (달력 그리드 대신, 메모가 있는 날짜만 목록으로 보여줌) --
        # 추가/제거/이전/다음 버튼은 위의 공용 cal_nav_buttons에만 있고, 이 서브탭에는 목록과
        # "공휴일 표시" 체크박스만 있음 (다른 서브탭과 같은 동작을 하는 버튼을 또 둘 필요가 없음)
        self._date_list_keys = []  # date_listbox의 각 행이 어떤 날짜인지 (표시 순서대로)

        # [공휴일 표시] 체크박스 - 목록 아래쪽에 고정. side=BOTTOM으로 목록(list_container)보다
        # 먼저 배치해야 expand=True로 채워지는 목록이 이 자리를 침범하지 않음. 체크 상태는
        # settings.ini에 저장되고, Alt+H(목록보기 서브탭이 활성일 때만 동작 - on_alt_h 참고)로도
        # 켜고 끌 수 있음
        list_bottom = ttk.Frame(list_tab)
        list_bottom.pack(side=tk.BOTTOM, fill=tk.X, padx=6, pady=(4, 8))
        self.show_holidays_var = tk.BooleanVar(
            value=self.app.settings_mgr.settings.get("show_holidays_in_list", False))
        self.show_holidays_check = ttk.Checkbutton(
            list_bottom, text="공휴일 표시", variable=self.show_holidays_var,
            command=self._on_toggle_show_holidays)
        self.show_holidays_check.pack(side=tk.LEFT)

        list_container = ttk.Frame(list_tab)
        list_container.pack(fill=tk.BOTH, expand=True, padx=6, pady=(8, 4))
        self.date_listbox = tk.Listbox(list_container, exportselection=False, font=UI_FONT)
        self.date_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        date_list_scroll = ttk.Scrollbar(list_container, orient="vertical", command=self.date_listbox.yview)
        date_list_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.date_listbox.config(yscrollcommand=date_list_scroll.set)
        self.date_listbox.bind("<<ListboxSelect>>", self._on_date_listbox_select)
        # 날짜 목록 단축키: 이 위젯에 직접 바인딩해서 날짜 목록에 포커스가 있을 때만 동작하게 함
        # (오른쪽 편집창의 Home/Delete 같은 기본 편집 동작과 섞이지 않음). Home/End는 Listbox
        # 기본 동작(가로 스크롤)을 대체하므로 핸들러가 "break"를 반환함. bind_when_visible로
        # 걸었으므로 목록이 화면에서 사라진 뒤에는 동작하지 않음
        bind_when_visible(self.date_listbox, "<Delete>", self._on_date_list_delete)
        bind_when_visible(self.date_listbox, "<Home>", self._on_date_list_home)
        bind_when_visible(self.date_listbox, "<End>", self._on_date_list_end)

        # ---- 오른쪽: 달력 메모 내용 (제목 필드 없음) ----
        cal_right = ttk.Frame(cal_container)
        cal_right.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.date_label_var = tk.StringVar(value=self._format_date_label(self.selected_date))
        ttk.Label(cal_right, textvariable=self.date_label_var, font=UI_FONT).pack(anchor="w")

        # height=1: content_text와 같은 이유(자연 요구 크기 최소화)
        self.date_content_text = tk.Text(cal_right, font=app.settings_mgr.content_font, padx=10, pady=8,
                                         height=1, **TEXT_UNDO_OPTIONS)
        self.date_content_text.pack(fill=tk.BOTH, expand=True)
        bind_redo_shortcuts(self.date_content_text)
        set_text_content(self.date_content_text, self.calendar_memos.get(self.selected_date, ""))
        self.date_content_text.bind("<KeyRelease>", self.save_date_memo_realtime)
        self.date_content_text.bind("<ButtonRelease-1>", self.app.update_status_bar)
        # PageUp/PageDown은 내용을 편집 중이어도 항상 이전/다음 메모로 이동해야 하므로,
        # Text의 기본 클래스 바인딩(페이지 스크롤)이 실행되기 전에 인스턴스 바인딩에서
        # break로 가로챔 (Listbox의 기본 B1-Motion 동작을 막을 때와 같은 방식)
        self.date_content_text.bind("<Prior>", self.app._on_prior_key)
        self.date_content_text.bind("<Next>", self.app._on_next_key)

        date_copy_frame = ttk.Frame(cal_right)
        date_copy_frame.pack(anchor="e", pady=5)
        self.date_copy_status_label = ttk.Label(date_copy_frame, text="", font=("맑은 고딕", 11, "bold"))
        self.date_copy_status_label.pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(date_copy_frame, text="클립보드로 복사", command=self.app.copy_to_clipboard).pack(side=tk.LEFT)

    # ---- MemoApp이 공통으로 호출하는 인터페이스 ----

    def set_content_font(self, font_tuple):
        self.date_content_text.config(font=font_tuple)

    def apply_theme_colors(self, colors):
        self.date_content_text.config(
            bg=colors["bg"], fg=colors["fg"],
            insertbackground=colors["insert_bg"],
            selectbackground=colors["text_select_bg"],
            selectforeground=colors["text_select_fg"],
            relief=tk.FLAT, borderwidth=0,
            highlightthickness=1,
            highlightbackground=colors["border"],
            highlightcolor=colors["accent"],
        )

        # 달력 요일 헤더(일~토) 라벨 색상
        for lbl, kind in self.weekday_label_widgets:
            if kind == "sun":
                lbl.config(bg=colors["bg"], fg=colors["sunday_fg"])
            elif kind == "sat":
                lbl.config(bg=colors["bg"], fg=colors["accent"])
            else:
                lbl.config(bg=colors["bg"], fg=colors["fg"])

        # 목록보기의 날짜 목록
        self.date_listbox.config(
            bg=colors["bg"], fg=colors["fg"],
            selectbackground=colors["list_select_bg"],
            selectforeground=colors["list_select_fg"],
            relief=tk.FLAT, borderwidth=0,
            highlightthickness=1,
            highlightbackground=colors["border"],
            highlightcolor=colors["accent"],
        )

        # 1년전체보기의 스크롤바 (항상 뚜렷하게 보이도록 기본 Tk 스크롤바 사용 - 테마색 적용)
        self.year_scrollbar.config(
            bg=colors["border"], troughcolor=colors["bg"],
            activebackground=colors["accent"], highlightthickness=0,
            relief=tk.FLAT, borderwidth=0,
        )

        # 달력 그리드: 칸 사이 여백이 은은한 격자선처럼 보이도록 배경색을 맞추고 다시 그림
        self.month_grid_frame.config(bg=colors["border"])
        self.render_month_view()
        self.year_grid_frame.config(bg=colors["border"])
        self.render_year_view()
        # 이 메서드는 (테마 적용의 부수효과로) 앱 시작 시 최초 1회 호출되는 지점이므로, 월별/
        # 1년전체 보기와 마찬가지로 목록보기도 여기서 한 번 그려야 처음 실행 후 목록보기 탭이
        # 비어 보이지 않음
        self._refresh_date_list()

    def get_status_text(self):
        memo_count = len(self.calendar_memos)
        status_text = f"총 {memo_count}개의 메모"
        if self.selected_date:
            cursor_pos = self.date_content_text.index(tk.INSERT)
            row, column = cursor_pos.split('.')
            row = int(row)
            column = int(column) + 1
            content = self.date_content_text.get("1.0", tk.END).strip()
            char_count = len(content)
            status_text += f" / 선택한 날짜: {self.selected_date} / 커서 위치: 줄 {row}, 열 {column} / 글자 수: {char_count}자"
        return status_text

    def get_copy_target(self):
        if not self.selected_date:
            return None
        return (self.date_content_text, self.date_copy_status_label)

    def on_activated(self, event=None):
        """탭 전환으로 이 탭이 선택되는 순간 호출됨.
        "오늘" 표시가 최신 날짜를 반영하도록 다시 그림(자정 경과 대비)."""
        if self._is_year_view_active():
            self.render_year_view()
            self._year_view_stale = False
        elif self._is_list_view_active():
            self._refresh_date_list()
            self._list_view_stale = False
        else:
            self.render_month_view()
            self._month_view_stale = False

    # ---- 탭 전용/공통 단축키 인터페이스 (MemoApp이 활성 탭에 위임함) ----

    def on_ctrl_d(self, event=None):
        return self.remove_date_memo()

    def focus_content(self, event=None):
        self.date_content_text.focus_set()
        return "break"

    def focus_primary(self, event=None):
        """Ctrl+T: 서브탭에 관계없이 오늘이 있는 달/해로 이동하고 오늘 날짜를 선택해 오른쪽
        편집창도 오늘 메모로 전환함 (go_to_today()가 처리). 1년전체보기의 [올해] 버튼은
        go_to_year만 호출해 화면 이동만 하고 선택 날짜는 바꾸지 않음."""
        self.go_to_today()
        return "break"

    def focus_list(self, event=None):
        """Ctrl+L: [목록보기] 서브탭으로 전환하고 날짜 목록에 포커스"""
        self.cal_view_notebook.select(2)
        self.date_listbox.focus_set()
        if not self.date_listbox.curselection() and self._date_list_keys:
            self.date_listbox.selection_set(0)
            self.date_listbox.activate(0)
        return "break"

    def on_ctrl_n(self, event=None):
        """Ctrl+N: [추가] 팝업 열기 (날짜를 직접 입력해 새 메모를 시작함).
        어느 서브탭(월별보기/1년전체보기/목록보기)에 있든 동일하게 동작함"""
        self._open_add_memo_dialog()
        return "break"

    def on_page_up(self, event=None):
        self.go_to_adjacent_memo_date(-1)
        return "break"

    def on_page_down(self, event=None):
        self.go_to_adjacent_memo_date(1)
        return "break"

    def insert_text_at_widget(self, widget, text):
        if widget is self.date_content_text:
            insert_text_as_one_undo_step(self.date_content_text, text)
            self.save_date_memo_realtime()
            return True
        return False

    # ---- 서브탭(월별보기/1년전체보기/목록보기) 및 날짜 이동 ----

    def _today_str(self):
        return datetime.now().strftime("%Y-%m-%d")

    def _format_date_label(self, date_key):
        try:
            d = datetime.strptime(date_key, "%Y-%m-%d")
            weekdays_kr = ["월", "화", "수", "목", "금", "토", "일"]
            return f"{date_key} ({weekdays_kr[d.weekday()]}) 메모 내용"
        except Exception:
            return f"{date_key} 메모 내용"

    def _is_year_view_active(self):
        try:
            return self.cal_view_notebook.index(self.cal_view_notebook.select()) == 1
        except Exception:
            return False

    def _is_list_view_active(self):
        try:
            return self.cal_view_notebook.index(self.cal_view_notebook.select()) == 2
        except Exception:
            return False

    def _on_cal_view_tab_changed(self, event=None):
        """[월별보기]/[1년전체보기]/[목록보기] 전환 시, 그 사이 다른 날짜를 클릭해
        갱신이 미뤄져 있었다면(성능을 위해 보이지 않는 뷰는 즉시 다시 그리지 않으므로)
        지금 그려준다."""
        if self._is_year_view_active():
            if getattr(self, "_year_view_stale", False):
                self.render_year_view()
                self._year_view_stale = False
        elif self._is_list_view_active():
            if getattr(self, "_list_view_stale", False):
                self._refresh_date_list()
                self._list_view_stale = False
        else:
            if getattr(self, "_month_view_stale", False):
                self.render_month_view()
                self._month_view_stale = False

    def _commit_month_year(self, event=None):
        try:
            y = int(self.month_year_var.get())
        except (ValueError, TypeError):
            y = self.cal_year
        # 직접 입력한 연도는 지원 범위 안으로 맞춤
        self.go_to_month(max(CAL_MIN_YEAR, min(CAL_MAX_YEAR, y)), self.cal_month)

    def _commit_year_year(self, event=None):
        try:
            y = int(self.year_year_var.get())
        except (ValueError, TypeError):
            y = self.cal_year_year
        self.go_to_year(max(CAL_MIN_YEAR, min(CAL_MAX_YEAR, y)))

    def _on_month_combo_change(self, event=None):
        try:
            m = int(self.month_month_var.get().replace("월", ""))
        except (ValueError, TypeError):
            m = self.cal_month
        self.go_to_month(self.cal_year, m)

    def _on_year_mousewheel(self, event):
        self.year_canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")

    def go_to_month(self, year, month):
        while month < 1:
            month += 12
            year -= 1
        while month > 12:
            month -= 12
            year += 1
        if not (CAL_MIN_YEAR <= year <= CAL_MAX_YEAR):
            # 지원 범위 밖으로 가는 이동(Alt+방향키 등)은 무시하고 입력창을 현재 값으로 되돌림
            self.month_year_var.set(str(self.cal_year))
            self.month_month_var.set(f"{self.cal_month}월")
            return
        self.cal_year, self.cal_month = year, month
        self.render_month_view()

    def go_to_year(self, year):
        if not (CAL_MIN_YEAR <= year <= CAL_MAX_YEAR):
            self.year_year_var.set(str(self.cal_year_year))
            return
        self.cal_year_year = year
        self.render_year_view()

    def go_to_today(self):
        """[월별보기]의 "오늘" 버튼: 오늘이 있는 달로 이동하고 오늘 날짜를 선택해 오른쪽
        편집창도 오늘 메모로 전환한다. ([1년전체보기]의 "올해" 버튼은 go_to_year를 그대로
        호출해 화면 이동만 하고 편집 중인 날짜는 바꾸지 않는다.)"""
        self.on_calendar_date_click(self._today_str())

    def on_calendar_date_click(self, date_key, redraw_list=True):
        """달력의 날짜 칸 클릭: 해당 날짜를 선택하고 오른쪽에 그 날짜의 메모 내용을 표시.
        (다른 달/해의 흐린 날짜를 클릭한 경우 그 달/해로 이동도 함께 처리)
        redraw_list=False는 [목록보기]에서 행을 직접 선택해 호출한 경우에 씀: 그 행은 이미
        선택되어 있고 메모 유무도 바뀌지 않으므로 목록을 다시 그릴 필요가 없음."""
        if normalize_date_key(date_key) is None:
            return  # 지원 연도(CAL_MIN_YEAR~CAL_MAX_YEAR) 밖의 흐린 날짜 칸
        try:
            y, m, _ = date_key.split("-")
            self.cal_year, self.cal_month = int(y), int(m)
            self.cal_year_year = int(y)
        except Exception:
            pass

        self.selected_date = date_key
        self.date_label_var.set(self._format_date_label(date_key))
        set_text_content(self.date_content_text, self.calendar_memos.get(date_key, ""))
        self._update_remove_date_memo_button_state()
        self._refresh_calendar_views(redraw_list=redraw_list)
        self.app.update_status_bar()

    def go_to_adjacent_memo_date(self, direction):
        """[◀이전]/[다음▶] 버튼 및 PageUp(-1)/PageDown(+1): 메모가 있는 날짜 중 현재 선택된
        날짜보다 이전/이후인 가장 가까운 날짜로 이동.
        (현재 선택된 날짜 자체에 메모가 없어도, 그 날짜를 기준으로 찾는다)"""
        if direction < 0:
            candidates = [d for d in self.calendar_memos if d < self.selected_date]
            if not candidates:
                messagebox.showinfo("알림", "이전 메모가 없습니다.")
                return
            target = max(candidates)
        else:
            candidates = [d for d in self.calendar_memos if d > self.selected_date]
            if not candidates:
                messagebox.showinfo("알림", "다음 메모가 없습니다.")
                return
            target = min(candidates)
        self.on_calendar_date_click(target)

    def _refresh_calendar_views(self, redraw_list=True):
        """현재 보이는 달력 뷰만 즉시 다시 그리고, 다른 쪽들은 다음에 그 탭으로
        전환될 때 그리도록 표시만 해둔다(불필요한 위젯 재생성을 피해 반응성을 유지).
        redraw_list=False면 [목록보기]가 보이는 중이어도 목록은 다시 그리지 않음
        (다른 뷰를 '나중에 그릴 것'으로 표시하는 일은 그대로 함)."""
        if self._is_year_view_active():
            self.render_year_view()
            self._month_view_stale = True
            self._list_view_stale = True
        elif self._is_list_view_active():
            if redraw_list:
                self._refresh_date_list()
            self._month_view_stale = True
            self._year_view_stale = True
        else:
            self.render_month_view()
            self._year_view_stale = True
            self._list_view_stale = True

    def save_date_memo_realtime(self, event=None):
        """달력메모 내용을 실시간으로 memos_calendar.json에 저장.
        (내용을 모두 지우면 해당 날짜 항목 자체를 제거해, 메모 표시 점과 파일을 깔끔하게 유지)"""
        if not self.selected_date:
            return
        had_memo = self.selected_date in self.calendar_memos
        # 빈 날짜 판정(자동 삭제 여부)에는 .strip()으로 공백만 있는지 보되, 저장하는 값은
        # 원본 그대로 써서 끝줄 공백/빈 줄이 사라지지 않게 함 ("end-1c"는 Tk가 붙이는 마지막
        # 개행 한 글자만 제외함)
        content = self.date_content_text.get("1.0", "end-1c")
        if content.strip():
            self.calendar_memos[self.selected_date] = content
        else:
            self.calendar_memos.pop(self.selected_date, None)
        self._update_remove_date_memo_button_state()
        self.app._debounced_save("calendar_memos", self.app.save_calendar_memos)
        # 달력 칸의 진한 배경색은 "메모 있음" 여부가 바뀔 때(빈 날짜에 처음 쓰거나 마지막
        # 내용을 지울 때)만 달라지므로, 그 순간에만 debounce로 달력 그리드를 다시 그림
        # (계속 타이핑하는 동안 칸을 재생성해 버벅이지 않고, 입력이 멈췄을 때 한 번만 반영됨)
        if had_memo != bool(content.strip()):
            self.app._debounced_save("calendar_view_refresh", self._refresh_calendar_views)
        self.app.update_status_bar()

    def _update_remove_date_memo_button_state(self):
        """[제거] 버튼(공용 하단 행의 [추가]/[제거]/[◀이전]/[다음▶] 중 하나)을 현재
        date_content_text 내용이 있을 때만 활성화. (Ctrl+D 단축키도 이 상태를 보고
        동작 여부를 결정함)"""
        has_content = bool(self.date_content_text.get("1.0", tk.END).strip())
        self.remove_date_memo_button.config(state=(tk.NORMAL if has_content else tk.DISABLED))

    def remove_date_memo(self, event=None):
        """[제거] 버튼 및 Ctrl+D: 선택된 날짜의 메모 내용을 확인 후 삭제.
        버튼이 비활성 상태(이미 내용 없음)면 아무 것도 하지 않음."""
        if str(self.remove_date_memo_button.cget("state")) != tk.NORMAL:
            return "break"
        if messagebox.askyesno("확인", f"{self.selected_date} 메모 내용을 삭제하시겠습니까?"):
            self.calendar_memos.pop(self.selected_date, None)
            self.app.save_calendar_memos()
            self.on_calendar_date_click(self.selected_date)
        return "break"

    # ---- 목록보기 ----

    def _refresh_date_list(self):
        """[목록보기]의 날짜 목록을 현재 메모가 있는 날짜만, 날짜순으로 다시 그림.
        [공휴일 표시] 체크박스가 켜져 있으면 holidays.json에 등록된 날짜 옆에
        "| 공휴일이름"을 덧붙임 (예: "2026-09-25 (금) | 추석")."""
        # 다시 그리면 스크롤이 맨 위로 초기화되므로, 맨 위에 보이던 날짜를 기억했다가 같은
        # 날짜(없으면 그 다음 날짜)가 맨 위에 오게 되돌림. 행 번호가 아니라 날짜로 기억하므로
        # 메모가 추가/삭제되어 행 수가 바뀌어도 보던 위치가 밀리지 않음.
        top_key = None
        if self.date_listbox.size() and self._date_list_keys:
            top_idx = self.date_listbox.nearest(0)
            if 0 <= top_idx < len(self._date_list_keys):
                top_key = self._date_list_keys[top_idx]
        self.date_listbox.delete(0, tk.END)
        self._date_list_keys = sorted(self.calendar_memos.keys())
        weekdays_kr = ["월", "화", "수", "목", "금", "토", "일"]
        show_holidays = self.show_holidays_var.get()
        for date_key in self._date_list_keys:
            try:
                d = datetime.strptime(date_key, "%Y-%m-%d")
                label = f"{date_key} ({weekdays_kr[d.weekday()]})"
            except Exception:
                label = date_key
            if show_holidays:
                holiday_name = self.holidays.get(date_key)
                if holiday_name:
                    label = f"{label} | {holiday_name}"
            self.date_listbox.insert(tk.END, label)
        if top_key is not None and self._date_list_keys:
            self.date_listbox.yview(min(bisect.bisect_left(self._date_list_keys, top_key),
                                        len(self._date_list_keys) - 1))
        if self.selected_date in self._date_list_keys:
            idx = self._date_list_keys.index(self.selected_date)
            self.date_listbox.selection_set(idx)
            self.date_listbox.activate(idx)
            self.date_listbox.see(idx)

    def _on_toggle_show_holidays(self):
        """[공휴일 표시] 체크박스(및 Alt+H)로 목록보기의 각 날짜 옆에 공휴일 이름을
        같이 보여줄지 전환하고, 다음 실행에도 기억하도록 settings.ini에 저장함"""
        self.app.settings_mgr.settings["show_holidays_in_list"] = self.show_holidays_var.get()
        self.app.settings_mgr.save()
        self._refresh_date_list()

    def on_alt_h(self, event=None):
        """Alt+H: [목록보기] 서브탭이 활성화되어 있을 때만 "공휴일 표시" 체크박스를
        켜고 끔 (다른 서브탭에서는 이 체크박스가 보이지 않으므로 아무 동작도 하지 않음)"""
        if not self._is_list_view_active():
            return None
        self.show_holidays_var.set(not self.show_holidays_var.get())
        self._on_toggle_show_holidays()
        return "break"

    def _on_date_listbox_select(self, event=None):
        sel = self.date_listbox.curselection()
        if not sel:
            return
        idx = sel[0]
        if 0 <= idx < len(self._date_list_keys):
            date_key = self._date_list_keys[idx]
            if date_key != self.selected_date:
                # 목록에서 직접 고른 행이므로 목록은 다시 그리지 않음 (다시 그리면 스크롤이
                # 맨 위로 초기화된 뒤 선택 행이 화면 가운데로 튀는 현상이 생김)
                self.on_calendar_date_click(date_key, redraw_list=False)

    def _on_date_list_delete(self, event=None):
        """날짜 목록에 포커스가 있을 때 Delete: 목록에서 선택한 날짜의 메모를 제거함.
        [제거] 버튼/Ctrl+D와 똑같이 확인 후 지움 (remove_date_memo 재사용).

        삭제 대상은 오른쪽 편집창의 날짜(selected_date)가 아니라 항상 "목록에서 선택된 행"
        기준임. 선택된 행이 없으면 아무 것도 하지 않아, 방금 쓰기 시작해서 아직 목록에 반영되지
        않은(debounce 대기 중) 날짜의 메모가 지워지는 일이 없도록 함."""
        sel = self.date_listbox.curselection()
        if not sel or not (0 <= sel[0] < len(self._date_list_keys)):
            return "break"
        idx = sel[0]
        date_key = self._date_list_keys[idx]
        if date_key != self.selected_date:
            # 평소에는 항상 일치하지만(행을 선택하면 selected_date도 따라 바뀜), 어긋나
            # 있더라도 remove_date_memo()가 엉뚱한 날짜를 지우지 않도록 먼저 맞춤
            self.on_calendar_date_click(date_key)
        self.remove_date_memo()
        # 확인창이 닫힌 뒤에도 키보드 포커스가 이 목록에 남아 방향키/Home/End를 이어서
        # 쓸 수 있도록 함
        self.date_listbox.focus_set()
        if date_key not in self.calendar_memos and self.date_listbox.size():
            # 지운 뒤 목록이 다시 그려지면 활성(active) 항목과 스크롤이 맨 위로 초기화되므로
            # 삭제한 자리로 되돌림 (선택은 하지 않음 - [제거] 버튼/Ctrl+D와 지운 뒤 상태를 같게 유지)
            near = min(idx, self.date_listbox.size() - 1)
            self.date_listbox.activate(near)
            self.date_listbox.see(near)
        return "break"

    def _on_date_list_home(self, event=None):
        """날짜 목록에 포커스가 있을 때 Home: 첫 번째 날짜로 이동 (방향키로 옮길 때처럼
        그 날짜를 선택해 오른쪽 편집창에 그 날짜의 메모를 표시함)"""
        focus_listbox_edge(self.date_listbox, to_end=False)
        return "break"

    def _on_date_list_end(self, event=None):
        """날짜 목록에 포커스가 있을 때 End: 마지막 날짜로 이동"""
        focus_listbox_edge(self.date_listbox, to_end=True)
        return "break"

    def _open_add_memo_dialog(self, event=None):
        """[추가] 버튼 및 Ctrl+N: 날짜를 직접 입력해 그 날짜로 이동함.
        (실제 메모 항목은 이동한 뒤 오른쪽 편집창에 내용을 입력해야 생김 - 달력메모는
        내용이 있어야만 "메모가 있다"고 취급함)"""
        dialog = Toplevel(self.app.root)
        dialog.title("메모 추가")
        dialog.resizable(False, False)
        dialog.transient(self.app.root)
        dialog.grab_set()
        dialog.focus_force()

        date_var = tk.StringVar(value=self._today_str())

        ttk.Label(dialog, text="날짜:", font=UI_FONT).grid(row=0, column=0, padx=(15, 5), pady=15, sticky="w")
        date_spin = ttk.Spinbox(dialog, textvariable=date_var, width=12, font=UI_FONT)
        date_spin.grid(row=0, column=1, padx=(0, 15), pady=15, sticky="w")
        date_spin.focus_set()
        date_spin.icursor(tk.END)

        def adjust_date(delta):
            try:
                d = datetime.strptime(date_var.get().strip(), "%Y-%m-%d").date()
            except ValueError:
                d = date.today()
            date_var.set((d + timedelta(days=delta)).strftime("%Y-%m-%d"))

        # ttk.Spinbox의 기본 클래스 바인딩은 <<Increment>>/<<Decrement>>에서 텍스트를 숫자로
        # 취급해 스스로 증감을 시도하므로(break 없음), 방금 넣은 날짜 문자열을 덮어쓰지 못하게
        # 반드시 "break"로 막아야 함
        def on_increment(e=None):
            adjust_date(1)
            return "break"

        def on_decrement(e=None):
            adjust_date(-1)
            return "break"

        date_spin.bind("<<Increment>>", on_increment)
        date_spin.bind("<<Decrement>>", on_decrement)

        def on_confirm(event=None):
            date_key = normalize_date_key(date_var.get())
            if date_key is None:
                messagebox.showerror(
                    "오류", f"날짜를 YYYY-MM-DD 형식({CAL_MIN_YEAR}~{CAL_MAX_YEAR}년)으로 입력하세요.",
                    parent=dialog)
                return
            already_exists = date_key in self.calendar_memos
            dialog.destroy()
            if already_exists:
                messagebox.showinfo("알림", "해당 날짜에는 이미 메모가 있습니다.", parent=self.app.root)
            self.on_calendar_date_click(date_key)
            if not already_exists:
                self.date_content_text.focus_set()

        def on_cancel():
            dialog.destroy()

        date_spin.bind("<Return>", on_confirm)
        dialog.bind("<Escape>", lambda e: on_cancel())

        button_frame = ttk.Frame(dialog)
        button_frame.grid(row=1, column=0, columnspan=2, pady=(0, 15))
        ttk.Button(button_frame, text="확인", command=on_confirm, width=10).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="취소", command=on_cancel, width=10).pack(side=tk.LEFT, padx=5)

    # ---- 렌더링 ----

    def render_month_view(self):
        """[월별보기] 그리드를 현재 self.cal_year/self.cal_month 기준으로 다시 그림
        (1년전체보기와 폭을 맞추기 위해 왼쪽에 빈 칸(0열)을 두고 요일 칸은 1~7열에 그림)"""
        self._hide_holiday_tooltip()  # 재구성 전, 떠 있을 수 있는 풍선말 정리
        for widget in self.month_grid_frame.winfo_children():
            widget.destroy()
        self.month_grid_frame.grid_columnconfigure(0, minsize=30)
        for c in range(1, 8):
            self.month_grid_frame.grid_columnconfigure(c, minsize=CAL_CELL_W + 2)

        year, month = self.cal_year, self.cal_month
        self.month_year_var.set(str(year))
        self.month_month_var.set(f"{month}월")

        first_weekday_mon0, total_days = calendar.monthrange(year, month)
        first_weekday = (first_weekday_mon0 + 1) % 7  # 월요일=0 -> 일요일=0 기준으로 변환

        prev_month = 12 if month == 1 else month - 1
        prev_year = year - 1 if month == 1 else year
        prev_days = calendar.monthrange(prev_year, prev_month)[1]

        next_month = 1 if month == 12 else month + 1
        next_year = year + 1 if month == 12 else year

        cells = []
        for i in range(first_weekday - 1, -1, -1):
            d = prev_days - i
            cells.append((d, f"{prev_year:04d}-{prev_month:02d}-{d:02d}", True))
        for d in range(1, total_days + 1):
            cells.append((d, f"{year:04d}-{month:02d}-{d:02d}", False))
        remainder = len(cells) % 7
        trailing = 0 if remainder == 0 else 7 - remainder
        for d in range(1, trailing + 1):
            cells.append((d, f"{next_year:04d}-{next_month:02d}-{d:02d}", True))

        # 0열은 1년전체보기와 폭을 맞추기 위한 빈 칸임. month_grid_frame 배경은 격자선 효과를
        # 위해 border색(회색)이라 아무 위젯도 없으면 이 칸만 회색 사각형으로 보이므로, 패널
        # 배경색(bg)의 빈 라벨을 각 행 0열에 채워 넣음 (1년전체보기가 월 숫자 라벨을 채우는 것과 같은 방식)
        colors = THEME_COLORS.get(self.app.settings_mgr.theme_mode, THEME_COLORS["light"])
        num_rows = len(cells) // 7
        for row in range(num_rows):
            tk.Label(self.month_grid_frame, text="", width=3, bg=colors["bg"]
                      ).grid(row=row, column=0, sticky="nsew", padx=1, pady=1)

        for idx, (day, key, other) in enumerate(cells):
            row, col = divmod(idx, 7)
            if other:
                kind = "other"
            elif col == 0:
                kind = "sun"
            elif col == 6:
                kind = "sat"
            else:
                kind = "normal"
            self._make_day_cell(self.month_grid_frame, row, col + 1, day, kind, key)

    def render_year_view(self):
        """[1년전체보기] 그리드를 현재 self.cal_year_year 기준으로 다시 그림
        (1월 1일이 속한 주의 일요일부터 12월 31일이 속한 주의 토요일까지 이어서 표시)"""
        self._hide_holiday_tooltip()  # 재구성 전, 떠 있을 수 있는 풍선말 정리
        for widget in self.year_grid_frame.winfo_children():
            widget.destroy()
        self.year_grid_frame.grid_columnconfigure(0, minsize=30)
        for c in range(1, 8):
            self.year_grid_frame.grid_columnconfigure(c, minsize=CAL_CELL_W + 2)

        year = self.cal_year_year
        self.year_year_var.set(str(year))
        colors = THEME_COLORS.get(self.app.settings_mgr.theme_mode, THEME_COLORS["light"])

        jan1 = date(year, 1, 1)
        start_pad = (jan1.weekday() + 1) % 7
        cursor = jan1 - timedelta(days=start_pad)

        dec31 = date(year, 12, 31)
        end_pad = 6 - ((dec31.weekday() + 1) % 7)
        end_date = dec31 + timedelta(days=end_pad)

        total_rows = ((end_date - cursor).days + 1) // 7

        d = cursor
        for r in range(total_rows):
            row_dates = [d + timedelta(days=c) for c in range(7)]
            d = d + timedelta(days=7)

            month_start = next((dt for dt in row_dates if dt.year == year and dt.day == 1), None)
            if month_start:
                label_cell = tk.Label(self.year_grid_frame, text=str(month_start.month), width=3,
                                       bg=colors["fg"], fg=colors["bg"], font=("맑은 고딕", 9, "bold"))
            else:
                label_cell = tk.Label(self.year_grid_frame, text="", width=3, bg=colors["bg"])
            label_cell.grid(row=r, column=0, sticky="nsew", padx=1, pady=1)

            for col, dt in enumerate(row_dates):
                in_year = dt.year == year
                key = dt.strftime("%Y-%m-%d")
                if not in_year:
                    kind = "other"
                elif col == 0:
                    kind = "sun"
                elif col == 6:
                    kind = "sat"
                else:
                    kind = "normal"
                self._make_day_cell(self.year_grid_frame, r, col + 1, dt.day, kind, key)

    def _make_day_cell(self, parent, row, col, day_num, kind, date_key):
        """달력의 날짜 한 칸을 그림(오늘=칠해진 원, 선택된 날짜=테두리 원, 메모 있음=진한 배경색)"""
        colors = THEME_COLORS.get(self.app.settings_mgr.theme_mode, THEME_COLORS["light"])
        has_memo = bool(str(self.calendar_memos.get(date_key, "")).strip())
        cell_bg = colors["has_memo_bg"] if has_memo else colors["bg"]
        canvas = tk.Canvas(parent, width=CAL_CELL_W, height=CAL_CELL_H,
                            highlightthickness=0, bg=cell_bg, cursor="hand2")
        canvas.grid(row=row, column=col, sticky="nsew", padx=1, pady=1)

        holiday_name = self.holidays.get(date_key)
        # 흐리게 표시되는 다른 달 날짜("other")는 일요일/토요일도 특별 색을 쓰지 않으므로,
        # 공휴일이어도 색을 강조하지 않음 (시각적 일관성)
        if kind == "other":
            fg = colors["muted_fg"]
            holiday_name = None
        elif holiday_name:
            fg = colors["sunday_fg"]  # 공휴일은 토요일이어도 일요일과 같은 빨간색
        elif kind == "sun":
            fg = colors["sunday_fg"]
        elif kind == "sat":
            fg = colors["accent"]
        else:
            fg = colors["fg"]

        cx, cy = CAL_CELL_W / 2, CAL_CELL_H / 2 - 2
        is_today = (date_key == self._today_str())
        is_selected = (date_key == self.selected_date)

        if is_today:
            r = 12
            canvas.create_oval(cx - r, cy - r, cx + r, cy + r, fill=colors["list_select_bg"], outline="")
            fg = colors["list_select_fg"]
        if is_selected:
            r = 14
            canvas.create_oval(cx - r, cy - r, cx + r, cy + r, outline=colors["accent"], width=2)

        canvas.create_text(cx, cy, text=str(day_num), fill=fg, font=("맑은 고딕", 10))

        canvas.bind("<Button-1>", lambda e, dk=date_key: self.on_calendar_date_click(dk))
        if holiday_name:
            canvas.bind("<Enter>", lambda e, name=holiday_name: self._show_holiday_tooltip(e, name))
            canvas.bind("<Leave>", self._hide_holiday_tooltip)
        return canvas

    def _show_holiday_tooltip(self, event, text):
        """공휴일 날짜 칸에 마우스를 올리면 공휴일 이름을 작은 풍선말로 표시.
        (공휴일 정보는 달력메모 내용이 아니라 이렇게 별도 풍선말로만 안내함)"""
        self._hide_holiday_tooltip()
        tooltip = tk.Toplevel(self.app.root)
        tooltip.wm_overrideredirect(True)
        try:
            tooltip.wm_attributes("-topmost", True)
        except tk.TclError:
            pass
        tooltip.wm_geometry(f"+{event.x_root + 12}+{event.y_root + 12}")
        tk.Label(tooltip, text=text, background="#ffffe0", foreground="#000000",
                 relief=tk.SOLID, borderwidth=1, font=("맑은 고딕", 9),
                 padx=6, pady=3).pack()
        self._holiday_tooltip = tooltip

    def _hide_holiday_tooltip(self, event=None):
        """떠 있는 공휴일 풍선말이 있으면 닫음"""
        if self._holiday_tooltip is not None:
            self._holiday_tooltip.destroy()
            self._holiday_tooltip = None

    # ---- 전용 단축키 (Alt+M/Y/L, Alt+←/→, Ctrl+Shift+D) ----
    # (아래 메서드들은 MemoApp이 "달력메모 탭이 활성화되어 있을 때만" 호출하므로 스스로
    # 활성 탭을 확인할 필요가 없음)

    def on_alt_m(self, event=None):
        """Alt+M: [월별보기] 서브탭 활성화
        (Ctrl+M은 이미 "메모 내용 편집창에 포커스"로 모든 탭에서 쓰이고 있어서
        서브탭 전환은 Alt 계열로 분리함)"""
        self.cal_view_notebook.select(0)
        return "break"

    def on_alt_y(self, event=None):
        """Alt+Y: [1년전체보기] 서브탭 활성화"""
        self.cal_view_notebook.select(1)
        return "break"

    def on_alt_l(self, event=None):
        """Alt+L: [목록보기] 서브탭 활성화"""
        self.cal_view_notebook.select(2)
        return "break"

    def on_alt_left(self, event=None):
        """Alt+왼쪽 방향키: 월별보기면 이전 달로, 1년전체면 이전 해로 이동"""
        if self._is_year_view_active():
            self.go_to_year(self.cal_year_year - 1)
        else:
            self.go_to_month(self.cal_year, self.cal_month - 1)
        return "break"

    def on_alt_right(self, event=None):
        """Alt+오른쪽 방향키: on_alt_left 참고 (반대 방향)"""
        if self._is_year_view_active():
            self.go_to_year(self.cal_year_year + 1)
        else:
            self.go_to_month(self.cal_year, self.cal_month + 1)
        return "break"

    def on_ctrl_shift_d(self, event=None):
        """Ctrl+Shift+D (고급 사용자용 숨김 기능, 버튼 없음): 특정 날짜 이전에
        저장된 달력메모를 한꺼번에 삭제하는 팝업. 일반메모는 작성/저장 날짜를
        따로 기록하지 않는 데이터 구조라 이 기능의 대상이 될 수 없으므로,
        달력메모(날짜별로 저장되는 메모)에만 적용됨."""
        dialog = Toplevel(self.app.root)
        dialog.title("메모 일괄 삭제")
        dialog.geometry("380x250")
        dialog.resizable(False, False)
        dialog.transient(self.app.root)
        dialog.grab_set()
        dialog.focus_force()

        default_date = (date.today() - timedelta(days=1)).strftime("%Y-%m-%d")
        date_var = tk.StringVar(value=default_date)

        ttk.Label(dialog, text="기준 날짜:", font=UI_FONT).grid(
            row=0, column=0, padx=10, pady=(15, 5), sticky="w")
        date_spin = ttk.Spinbox(dialog, textvariable=date_var, width=12, font=UI_FONT)
        date_spin.grid(row=0, column=1, padx=10, pady=(15, 5), sticky="w")
        date_spin.focus_set()
        date_spin.icursor(tk.END)

        def adjust_date(delta):
            """스핀박스 위/아래 버튼: 날짜를 하루씩 증가/감소 (월/연 경계도 올바르게 처리)"""
            try:
                d = datetime.strptime(date_var.get().strip(), "%Y-%m-%d").date()
            except ValueError:
                d = date.today() - timedelta(days=1)
            date_var.set((d + timedelta(days=delta)).strftime("%Y-%m-%d"))

        # <<Increment>>/<<Decrement>>의 기본 증감을 "break"로 막는 이유는 [추가] 팝업과 같음
        def on_increment(e=None):
            adjust_date(1)
            return "break"

        def on_decrement(e=None):
            adjust_date(-1)
            return "break"

        date_spin.bind("<<Increment>>", on_increment)
        date_spin.bind("<<Decrement>>", on_decrement)

        colors = THEME_COLORS.get(self.app.settings_mgr.theme_mode, THEME_COLORS["light"])
        desc = (
            "선택한 날짜를 포함하여 그 이전 날짜에 저장된 달력메모 내용을\n"
            "모두 삭제합니다.\n\n"
            f"※ 삭제 직전에 현재 데이터가 {AUTO_BACKUP_DIRNAME} 폴더에 자동 백업됩니다.\n"
            "   그래도 날짜를 확인한 뒤 실행하세요."
        )
        ttk.Label(dialog, text=desc, font=("맑은 고딕", 9), foreground=colors["sunday_fg"],
                  justify=tk.LEFT).grid(row=1, column=0, columnspan=2, padx=10, pady=10, sticky="w")

        def on_confirm():
            raw = date_var.get().strip()
            try:
                cutoff = datetime.strptime(raw, "%Y-%m-%d").date().strftime("%Y-%m-%d")
            except ValueError:
                messagebox.showerror("오류", "날짜를 YYYY-MM-DD 형식으로 입력하세요.", parent=dialog)
                return
            to_delete = [d for d in self.calendar_memos if d <= cutoff]
            backup_path = None
            if to_delete:
                proceed, backup_path = self.app.auto_backup_before("before-bulk-delete", parent=dialog)
                if not proceed:
                    return
            for d in to_delete:
                del self.calendar_memos[d]
            self.app.save_calendar_memos()
            self._refresh_calendar_views()
            self.on_calendar_date_click(self.selected_date)
            dialog.destroy()
            if to_delete:
                messagebox.showinfo(
                    "완료", f"{len(to_delete)}개의 달력메모를 삭제했습니다." + self.app.backup_note(backup_path))
            else:
                messagebox.showinfo("완료", "삭제할 메모가 없습니다.")

        def on_cancel():
            dialog.destroy()

        dialog.bind("<Escape>", lambda e: on_cancel())

        button_frame = ttk.Frame(dialog)
        button_frame.grid(row=2, column=0, columnspan=2, pady=15)
        ttk.Button(button_frame, text="확인", command=on_confirm, width=10).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="취소", command=on_cancel, width=10).pack(side=tk.LEFT, padx=5)

    # ---- 가져오기/내보내기/백업 훅 (일반메모 탭의 같은 절 설명 참고) ----

    transfer_label = "달력메모"
    transfer_filename = "memos_calendar.json"

    def transfer_parse(self, raw):
        """memos_calendar.json과 같은 {"YYYY-MM-DD": "내용"} 형태인지 검증 (잘못되면 TypeError/ValueError)"""
        if not isinstance(raw, dict):
            raise TypeError('데이터가 {"날짜": "내용"} 형태의 딕셔너리가 아닙니다.')
        memos, skipped = normalize_calendar_memos(raw)
        if skipped:
            raise ValueError(
                f"날짜(YYYY-MM-DD, {CAL_MIN_YEAR}~{CAL_MAX_YEAR}년) 형식이 아니거나 내용이 문자열이 아닌 "
                f"항목이 있습니다: {skipped[0]!r}")
        return memos

    def transfer_summary(self, data):
        return f"메모 {len(data)}개"

    def transfer_apply(self, data):
        self.calendar_memos = data
        ok = self.app.save_calendar_memos()
        set_text_content(self.date_content_text, self.calendar_memos.get(self.selected_date, ""))
        self._update_remove_date_memo_button_state()
        self.render_month_view()
        self.render_year_view()
        self._refresh_date_list()
        self._month_view_stale = False
        self._year_view_stale = False
        self._list_view_stale = False
        self.app.update_status_bar()
        return ok

    def transfer_export_json(self):
        return dict(sorted(self.calendar_memos.items()))  # 날짜 오름차순

    def transfer_export_txt(self):
        return "".join(
            f"{date_key}\n" + "-" * 20 + f"\n{content}\n\n" + "=" * 20 + "\n\n"
            for date_key, content in sorted(self.calendar_memos.items()))

    def transfer_export_xlsx(self):
        return "달력메모", ["날짜", "내용"], [[k, v] for k, v in sorted(self.calendar_memos.items())]


# ============================================================================
# "컬렉션" 탭 (컬렉션/항목 CRUD, URL 제목 자동 수집, 순서 변경)
# ============================================================================

class TitleFetcher:
    """별도 스레드에서 URL의 <title>을 가져와 큐에 결과를 전달함.

    제목 추출 순서
    -------------
    1) <head> 영역을 먼저 잘라내고, 그 안에서 <title>...</title>을 그대로 추출.
       (본문에 섞여 있는 SVG 아이콘의 <title> 등을 잘못 집어오는 것을 방지)
    2) <head>를 못 찾았거나 <title>이 비어 있으면, 문서 전체에서 다시 <title>을 찾음.
    3) 그래도 없으면 <meta property="og:title"> / <meta name="twitter:title">를 보조로 사용.

    결과는 다음과 같은 딕셔너리로 큐에 전달됨: {"request_id": str, "title": str|None, "error": str|None}
    """

    TITLE_RE = re.compile(r"<title[^>]*>(.*?)</title>", re.IGNORECASE | re.DOTALL)
    HEAD_RE = re.compile(r"<head[^>]*>(.*?)</head>", re.IGNORECASE | re.DOTALL)
    META_TAG_RE = re.compile(r"<meta\b[^>]*>", re.IGNORECASE)
    ATTR_RE = re.compile(r"([\w:-]+)\s*=\s*\"([^\"]*)\"|([\w:-]+)\s*=\s*'([^']*)'", re.IGNORECASE)
    CHARSET_HEADER_RE = re.compile(r"charset=([\w\-]+)", re.IGNORECASE)
    CHARSET_META_RE = re.compile(rb'charset=["\']?\s*([\w\-]+)', re.IGNORECASE)

    REQUEST_TIMEOUT = 8
    # timeout은 "한 번의 읽기를 기다리는 시간"이라 큰 파일이나 조금씩 계속 오는 응답은 못 막으므로,
    # 본문은 앞쪽 MAX_HTML_BYTES까지만 읽고(제목은 문서 앞부분에 있음), 요청 하나가 끝나기까지의
    # 전체 시간은 MAX_TOTAL_SECONDS로 제한함 (fetch_async 참고)
    MAX_HTML_BYTES = 512 * 1024
    MAX_TOTAL_SECONDS = 20
    USER_AGENT = (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
    )
    REQUEST_HEADERS = {
        "User-Agent": USER_AGENT,
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8",
        "Accept-Language": "ko-KR,ko;q=0.9,en-US;q=0.8,en;q=0.7",
        # br(Brotli)은 brotli 패키지가 없으면 requests가 풀지 못해 본문이 깨지므로 알리지 않음
        "Accept-Encoding": "gzip, deflate",
        "Upgrade-Insecure-Requests": "1",
    }

    def __init__(self, result_queue):
        self.result_queue = result_queue

    def fetch_async(self, url, request_id):
        thread = threading.Thread(target=self._fetch_with_deadline, args=(url, request_id), daemon=True)
        thread.start()

    def _fetch_with_deadline(self, url, request_id):
        """_fetch를 작업 스레드에서 돌리고, MAX_TOTAL_SECONDS 안에 끝나지 않으면 시간 초과로 알림.
        (요청 라이브러리에는 전체 시간 제한이 없고, 응답이 조금씩 계속 오면 읽기가 끝나지 않아
        '가져오는 중' 상태로 남기 때문) 작업 스레드는 요청마다 따로 만든 큐에 결과를 넣으므로,
        시간 초과로 포기한 작업이 나중에 끝나도 그 결과가 앱에 전달되지는 않음."""
        private_queue = queue.Queue()
        worker = threading.Thread(
            target=type(self)(private_queue)._fetch, args=(url, request_id), daemon=True)
        worker.start()
        worker.join(self.MAX_TOTAL_SECONDS)
        try:
            result = private_queue.get_nowait()
        except queue.Empty:
            result = {"request_id": request_id, "title": None, "error": "요청 시간이 초과되었습니다."}
        self.result_queue.put(result)

    def _put(self, request_id, title=None, error=None):
        self.result_queue.put({"request_id": request_id, "title": title, "error": error})

    def _fetch(self, url, request_id):
        if requests is None:
            self._put(request_id, error="requests 라이브러리가 설치되어 있지 않습니다.")
            return
        try:
            with requests.get(
                url, headers=self.REQUEST_HEADERS, timeout=self.REQUEST_TIMEOUT, allow_redirects=True,
                stream=True,
            ) as resp:
                resp.raise_for_status()
                content_type = resp.headers.get("Content-Type", "")
                mime = content_type.split(";")[0].strip().lower()
                # PDF/이미지/압축파일 같은 것은 내려받지 않고 바로 알림 (Content-Type이 없으면 시도함)
                if mime and not (mime.startswith("text/") or "html" in mime or "xml" in mime):
                    self._put(request_id, error=f"웹 페이지(HTML)가 아니라서 제목을 가져올 수 없습니다 ({mime})")
                    return
                raw = self._read_limited(resp)
            html_text = self._decode(raw, content_type)

            head_match = self.HEAD_RE.search(html_text)
            head_html = head_match.group(1) if head_match else None
            meta_scope = head_html or html_text

            # 1순위: <head> 안의 <title>
            title = self._clean_title(self._search_title(head_html)) if head_html else ""
            # 2순위: <head>를 못 찾았거나 그 안에 <title>이 없는 경우, 문서 전체에서 재검색
            if not title:
                title = self._clean_title(self._search_title(html_text))
            # 3순위: 그래도 없으면 og:title / twitter:title 메타 태그
            if not title:
                title = self._clean_title(self._search_meta_content(meta_scope, ("og:title", "twitter:title")))

            if title:
                self._put(request_id, title=title)
            else:
                self._put(request_id, error="페이지에서 제목을 찾을 수 없습니다.")
        except requests.exceptions.Timeout:
            self._put(request_id, error="요청 시간이 초과되었습니다.")
        except requests.exceptions.SSLError:
            self._put(request_id, error="보안 연결(SSL)에 실패했습니다.")
        except requests.exceptions.RequestException as exc:
            status = getattr(getattr(exc, "response", None), "status_code", None)
            if status:
                self._put(request_id, error=f"페이지를 가져올 수 없습니다 (HTTP {status})")
            else:
                self._put(request_id, error=f"페이지를 가져올 수 없습니다 ({exc.__class__.__name__})")
        except Exception as exc:  # 백그라운드 스레드가 죽지 않도록 모든 예외를 포착
            self._put(request_id, error=f"알 수 없는 오류: {exc}")

    def _search_title(self, html_fragment):
        if not html_fragment:
            return None
        match = self.TITLE_RE.search(html_fragment)
        return match.group(1) if match else None

    def _search_meta_content(self, html_fragment, keys):
        """<meta property="..." content="..."> 또는 name= 형태에서 keys에 해당하는 content 값을 찾음."""
        if not html_fragment:
            return None
        for tag in self.META_TAG_RE.findall(html_fragment):
            attrs = {}
            for m in self.ATTR_RE.finditer(tag):
                if m.group(1) is not None:
                    attrs[m.group(1).lower()] = m.group(2)
                else:
                    attrs[m.group(3).lower()] = m.group(4)
            key = (attrs.get("property") or attrs.get("name") or "").lower()
            if key in keys and attrs.get("content"):
                return attrs["content"]
        return None

    def _read_limited(self, resp):
        """응답 본문을 앞에서부터 읽되 MAX_HTML_BYTES를 넘으면 거기서 멈추고 읽은 데까지만 반환함
        (gzip 등은 풀린 크기 기준). 읽는 도중 연결이 끊겨도 이미 받은 부분이 있으면 그것으로
        제목을 찾아봄."""
        chunks, size = [], 0
        try:
            for chunk in resp.iter_content(chunk_size=32768):
                if not chunk:
                    continue
                chunks.append(chunk)
                size += len(chunk)
                if size >= self.MAX_HTML_BYTES:
                    break
        except requests.exceptions.RequestException:
            if not chunks:
                raise
        return b"".join(chunks)[:self.MAX_HTML_BYTES]

    @classmethod
    def _decode(cls, raw, content_type):
        """바이트를 문자열로 바꿈 (알 수 없는 인코딩 이름이면 UTF-8, 깨진 글자는 대체 문자로)"""
        encoding = cls._resolve_encoding(content_type, raw)
        try:
            return raw.decode(encoding, errors="replace")
        except (LookupError, TypeError):
            return raw.decode("utf-8", errors="replace")

    @classmethod
    def _resolve_encoding(cls, content_type, raw):
        # 1순위: HTTP 응답 헤더의 charset
        header_match = cls.CHARSET_HEADER_RE.search(content_type)
        if header_match:
            return header_match.group(1)
        # 2순위: HTML 문서 안의 <meta charset="..."> (한글 사이트에서 euc-kr/cp949가 자주 쓰임)
        meta_match = cls.CHARSET_META_RE.search(raw[:4096])
        if meta_match:
            try:
                encoding = meta_match.group(1).decode("ascii", errors="ignore").strip("\"' ")
                if encoding:
                    return encoding
            except Exception:
                pass
        # 3순위: UTF-8로 읽히면 UTF-8 (UTF-8이 아닌 글이 우연히 UTF-8로 읽힐 가능성은 매우 낮음.
        # 앞부분만 읽어 끝이 글자 중간에서 잘렸을 수 있으므로 잘린 끝은 허용함)
        try:
            codecs.getincrementaldecoder("utf-8")().decode(raw, final=False)
            return "utf-8"
        except UnicodeDecodeError:
            pass
        # 4순위: requests가 쓰는 인코딩 추정기(chardet 등)로 추정 (느릴 수 있어 앞부분만 사용)
        detect = getattr(getattr(requests.compat, "chardet", None), "detect", None)
        if detect:
            try:
                guess = detect(raw[:65536]).get("encoding")
                if guess:
                    return guess
            except Exception:
                pass
        # 추정기가 없거나 실패하면 한글 윈도우 기본 인코딩(cp949)
        return "cp949"

    @staticmethod
    def _clean_title(raw):
        if not raw:
            return ""
        text = html.unescape(raw)
        text = re.sub(r"\s+", " ", text).strip()
        return text


class EditItemDialog(tk.Toplevel):
    """항목(링크/메모) 편집 창: 제목/URL/메모 세 필드를 편집함."""

    def __init__(self, parent, item, on_save, content_font, colors):
        super().__init__(parent)
        self.title("항목 편집")
        self.resizable(False, False)
        self.transient(parent)
        self.on_save = on_save

        frame = ttk.Frame(self, padding=16)
        frame.pack(fill="both", expand=True)

        ttk.Label(frame, text="제목", font=UI_FONT).grid(row=0, column=0, sticky="w")
        self.title_var = tk.StringVar(value=item.get("title", ""))
        title_entry = ttk.Entry(frame, textvariable=self.title_var, width=48, font=UI_FONT)
        title_entry.grid(row=1, column=0, pady=(2, 10))

        ttk.Label(frame, text="URL (선택 사항 — 비워두면 메모 항목이 됩니다)", font=UI_FONT).grid(
            row=2, column=0, sticky="w")
        self.url_var = tk.StringVar(value=item.get("url", ""))
        url_entry = ttk.Entry(frame, textvariable=self.url_var, width=48, font=UI_FONT)
        url_entry.grid(row=3, column=0, pady=(2, 10))

        ttk.Label(frame, text="메모 (여러 줄 입력 가능 · 저장: Ctrl+Enter)", font=UI_FONT).grid(
            row=4, column=0, sticky="w")
        self.memo_text = tk.Text(
            frame, width=48, height=8, font=content_font, wrap="word",
            bg=colors["bg"], fg=colors["fg"], insertbackground=colors["insert_bg"],
            selectbackground=colors["text_select_bg"], selectforeground=colors["text_select_fg"],
            relief=tk.FLAT, borderwidth=0, highlightthickness=1,
            highlightbackground=colors["border"], highlightcolor=colors["accent"],
            **TEXT_UNDO_OPTIONS,
        )
        bind_redo_shortcuts(self.memo_text)
        set_text_content(self.memo_text, item.get("memo", ""))
        self.memo_text.grid(row=5, column=0, pady=(2, 14))

        btn_frame = ttk.Frame(frame)
        btn_frame.grid(row=6, column=0, sticky="e")
        ttk.Button(btn_frame, text="취소", command=self.destroy).pack(side="right")
        ttk.Button(btn_frame, text="저장", command=self._save).pack(side="right", padx=(0, 8))

        title_entry.bind("<Return>", lambda e: self._save())
        url_entry.bind("<Return>", lambda e: self._save())
        self.memo_text.bind("<Control-Return>", lambda e: self._save())
        self.bind("<Escape>", lambda e: self.destroy())

        self.grab_set()
        title_entry.focus_set()
        title_entry.select_range(0, "end")

    def _save(self):
        title = self.title_var.get().strip()
        url = self.url_var.get().strip()
        memo = self.memo_text.get("1.0", "end-1c").strip()
        if not url and not title and not memo:
            messagebox.showwarning("입력 오류", "제목, URL, 메모 중 하나는 입력해야 합니다.", parent=self)
            return
        if url:
            url = normalize_url(url)
            if not is_web_url(url):
                messagebox.showwarning(
                    "입력 오류", "URL은 http:// 또는 https:// 웹 주소만 입력할 수 있습니다.", parent=self)
                return
        self.on_save(title or url, url, memo)
        self.destroy()


def shortcuts_file_path():
    """단축키 안내 파일(shortcuts.md)의 경로: 프로그램(exe 또는 ad.py)과 같은 폴더"""
    return os.path.join(get_app_dir(), SHORTCUTS_FILE_NAME)


def _strip_inline_markdown(text):
    """표 셀/문장 안의 간단한 Markdown 서식 기호를 없애고 화면에 보일 글자만 남김.
    GitHub에서 보기 좋게 `Ctrl+N`(코드)이나 **굵게**를 써도 안내 창에는 기호 없이 표시됨.
    <br>은 줄바꿈으로, \\|는 | 문자로 바꿈."""
    text = re.sub(r"<br\s*/?>", "\n", text, flags=re.IGNORECASE)
    text = re.sub(r"`([^`]*)`", r"\1", text)
    text = re.sub(r"\*\*(.+?)\*\*", r"\1", text)
    text = text.replace("\\|", "|")
    return text.strip()


def _split_table_row(line):
    """'| 단축키 | 설명 |' 표 한 줄을 셀 목록으로 나눔. 이스케이프한 \\|는 구분자로 보지 않음"""
    line = line.strip()
    if line.startswith("|"):
        line = line[1:]
    if line.endswith("|") and not line.endswith("\\|"):
        line = line[:-1]
    return [cell.strip() for cell in re.split(r"(?<!\\)\|", line)]


def _is_table_separator(cells):
    """'|---|:---:|' 같은 표 구분선 행인지"""
    return bool(cells) and all(re.fullmatch(r":?-+:?", cell) for cell in cells)


def parse_shortcut_guide(text):
    """shortcuts.md 내용을 안내 창에 그릴 블록 목록으로 바꿈. 형식이 어긋난 줄이 있어도
    예외를 내지 않고 일반 문장으로 보여줌. 블록 종류:
      ("heading", 단계(1~6), 제목)  # / ## / ### 제목
      ("row", 단축키, 설명)         | 단축키 | 설명 | 표의 한 줄 (표 머리글 행과 |---| 줄은 제외)
      ("text", 문장)                그 밖의 문장, "- " 목록(• 로 표시), "> " 인용
      ("rule",)                     --- 가로줄
    <!-- --> 주석은 여러 줄이어도 통째로 무시함."""
    text = re.sub(r"<!--.*?-->", "", text, flags=re.DOTALL)
    lines = text.splitlines()
    blocks = []
    i = 0
    while i < len(lines):
        raw = lines[i].strip()
        i += 1
        if not raw:
            continue

        m = re.match(r"^(#{1,6})\s+(.+)$", raw)
        if m:
            title = _strip_inline_markdown(re.sub(r"\s+#+$", "", m.group(2)))
            if title:
                blocks.append(("heading", len(m.group(1)), title))
            continue

        if raw.startswith("|"):
            cells = _split_table_row(raw)
            if _is_table_separator(cells):
                continue
            if (i < len(lines) and lines[i].strip().startswith("|")
                    and _is_table_separator(_split_table_row(lines[i]))):
                i += 1  # 바로 아래가 구분선이면 이 줄은 표 머리글 행 - 표시하지 않음
                continue
            if len(cells) >= 2:
                key = _strip_inline_markdown(cells[0])
                desc = _strip_inline_markdown(" | ".join(cells[1:]))
                if key or desc:
                    blocks.append(("row", key, desc))
            else:
                t = _strip_inline_markdown(cells[0])
                if t:
                    blocks.append(("text", t))
            continue

        if re.fullmatch(r"[-*_]{3,}", raw.replace(" ", "")):
            blocks.append(("rule",))
            continue

        m = re.match(r"^[-*+]\s+(.+)$", raw)
        if m:
            t = _strip_inline_markdown(m.group(1))
            if t:
                blocks.append(("text", "• " + t))
            continue

        m = re.match(r"^>\s?(.*)$", raw)
        t = _strip_inline_markdown(m.group(1) if m else raw)
        if t:
            blocks.append(("text", t))
    return blocks


def load_shortcut_guide():
    """shortcuts.md를 읽어 (블록 목록, 오류 메시지)를 반환함. 성공하면 오류 메시지는 None.
    파일이 없거나 읽을 수 없거나 내용이 비어 있으면 블록 목록이 비고 오류 메시지가 채워짐
    (안내 창이 예외로 죽는 대신 그 이유를 창 안에 보여주기 위함).
    UTF-8(BOM 유무 무관)로 읽고, 실패하면 CP949로 다시 시도함."""
    path = shortcuts_file_path()
    if not os.path.isfile(path):
        return [], (f"단축키 안내 파일({SHORTCUTS_FILE_NAME})을 찾을 수 없습니다.\n\n"
                    f"프로그램과 같은 폴더에 {SHORTCUTS_FILE_NAME} 파일을 두면 이 창에 표시됩니다.\n\n"
                    f"확인한 위치:\n{path}")
    text = None
    for encoding in ("utf-8-sig", "cp949"):
        try:
            with open(path, "r", encoding=encoding) as f:
                text = f.read()
            break
        except UnicodeDecodeError:
            continue
        except OSError as e:
            return [], f"단축키 안내 파일을 읽지 못했습니다.\n\n{path}\n\n{e}"
    if text is None:
        return [], (f"단축키 안내 파일({SHORTCUTS_FILE_NAME})의 글자 인코딩을 알 수 없습니다.\n\n"
                    "UTF-8로 다시 저장해 주세요.\n(메모장: 다른 이름으로 저장 > 인코딩 UTF-8)")
    blocks = parse_shortcut_guide(text)
    if not blocks:
        return [], f"{SHORTCUTS_FILE_NAME}에 표시할 내용이 없습니다.\n\n{path}"
    return blocks, None


class ShortcutHelpDialog(tk.Toplevel):
    """F1 / [도움말 > 단축키 안내]: shortcuts.md의 내용을 보여주는 창.

    안내 문구는 코드가 아니라 프로그램과 같은 폴더의 shortcuts.md에 있음. 창을 열 때마다
    파일을 새로 읽으므로, 파일을 고치면 프로그램을 다시 켜지 않아도 다음에 열 때 반영됨.
    파일이 없거나 읽을 수 없으면 창 안에 그 이유를 보여줌.

    화면 구성은 섹션 제목 / 강조색 단축키 + 설명(2열) / 일반 문장. 창 크기를 바꾸면 긴
    설명은 줄바꿈되고, 내용이 길면 스크롤됨 (마우스 휠, 스크롤바, ↑↓ PageUp/PageDown
    Home/End). 창을 닫을 때 정리해야 하는 전역 바인딩은 만들지 않음."""

    KEY_FONT = ("맑은 고딕", 9, "bold")
    # Markdown 제목 단계별 글꼴 (# = 1, ## = 2, 그 밖에는 HEADING_FONT_DEFAULT)
    HEADING_FONTS = {1: ("맑은 고딕", 13, "bold"), 2: ("맑은 고딕", 11, "bold")}
    HEADING_FONT_DEFAULT = ("맑은 고딕", 10, "bold")
    KEY_PAD = (14, 18)  # 단축키 열 좌우 여백
    TEXT_INDENT = 14  # 일반 문장의 왼쪽 여백

    def __init__(self, parent, colors):
        super().__init__(parent)
        self.title("단축키 안내")
        scale = max(1.0, self.winfo_fpixels("1i") / 96.0)
        self.minsize(int(380 * scale), int(260 * scale))
        self.transient(parent)

        # 창을 줄여도 [닫기] 버튼과 스크롤바가 가려지지 않도록 먼저(가장자리에) 배치함
        close_btn = ttk.Button(self, text="닫기", command=self.destroy)
        close_btn.pack(side="bottom", pady=(0, 12))

        outer = ttk.Frame(self, padding=16)
        outer.pack(fill="both", expand=True)

        self._canvas = canvas = tk.Canvas(outer, highlightthickness=0, bg=colors["bg"], yscrollincrement=20)
        vsb = ttk.Scrollbar(outer, orient="vertical", command=canvas.yview)
        canvas.configure(yscrollcommand=vsb.set)
        vsb.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)

        inner = ttk.Frame(canvas)
        inner.columnconfigure(1, weight=1)
        self._inner_id = canvas.create_window((0, 0), window=inner, anchor="nw")
        inner.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))

        self._key_col_width = 0  # 가장 긴 단축키의 줄바꿈 전 폭 (아래에서 측정)
        self._key_labels = []  # 단축키(1열) 라벨
        self._desc_labels = []  # 설명(2열) 라벨
        self._wide_labels = []  # 제목/문장처럼 두 열에 걸치는 (라벨, 왼쪽 여백)
        blocks, error = load_shortcut_guide()
        if error:
            blocks = [("text", error)]
        self._build_content(inner, blocks, colors)

        # 처음 크기: 줄바꿈 없이 내용이 다 보이는 크기(가로 700px, 화면의 80%, 세로 화면의 70%까지)
        self.update_idletasks()
        self._key_col_width = max((lbl.winfo_reqwidth() for lbl in self._key_labels), default=0)
        width = max(int(460 * scale), min(inner.winfo_reqwidth(), int(700 * scale),
                                          int(self.winfo_screenwidth() * 0.8)))
        height = max(int(260 * scale), min(inner.winfo_reqheight(), int(self.winfo_screenheight() * 0.7)))
        canvas.configure(width=width, height=height)
        self._apply_wrap(width)
        # 창 크기가 바뀔 때마다 줄바꿈을 다시 맞춤. 위에서 폭을 측정하기 전에 호출되면 안 되므로
        # (측정 중에도 Configure 이벤트가 발생함) 측정이 끝난 뒤에 바인딩함
        canvas.bind("<Configure>", self._on_canvas_configure)

        # 스크롤: 전역(bind_all)이 아니라 이 창(Toplevel)에만 바인딩함. 자식 위젯의 이벤트도 여기까지
        # 전달되므로 창 어디서든 동작하고, 창이 닫히면 바인딩도 함께 사라짐
        self.bind("<MouseWheel>", self._on_mousewheel)
        self.bind("<Up>", lambda e: canvas.yview_scroll(-1, "units"))
        self.bind("<Down>", lambda e: canvas.yview_scroll(1, "units"))
        self.bind("<Prior>", lambda e: canvas.yview_scroll(-1, "pages"))
        self.bind("<Next>", lambda e: canvas.yview_scroll(1, "pages"))
        self.bind("<Home>", lambda e: canvas.yview_moveto(0))
        self.bind("<End>", lambda e: canvas.yview_moveto(1))
        self.bind("<Escape>", lambda e: self.destroy())

        try:
            self.grab_set()
        except tk.TclError:
            pass  # 창이 아직 화면에 나타나기 전이면 실패할 수 있음 - 안내 창이라 치명적이지 않음
        close_btn.focus_set()

    def _build_content(self, inner, blocks, colors):
        row = 0
        for block in blocks:
            kind = block[0]
            if kind == "heading":
                _, level, title = block
                font = self.HEADING_FONTS.get(level, self.HEADING_FONT_DEFAULT)
                lbl = ttk.Label(inner, text=title, font=font)
                lbl.grid(row=row, column=0, columnspan=2, sticky="w", pady=(12 if row else 0, 6))
                self._wide_labels.append((lbl, 0))
            elif kind == "row":
                _, key, desc = block
                key_lbl = ttk.Label(inner, text=key, font=self.KEY_FONT, foreground=colors["accent"])
                key_lbl.grid(row=row, column=0, sticky="nw", padx=self.KEY_PAD, pady=(4, 2))
                desc_lbl = ttk.Label(inner, text=desc, font=UI_FONT)
                desc_lbl.grid(row=row, column=1, sticky="nw", pady=2)
                self._key_labels.append(key_lbl)
                self._desc_labels.append(desc_lbl)
            elif kind == "rule":
                ttk.Separator(inner, orient="horizontal").grid(
                    row=row, column=0, columnspan=2, sticky="ew", pady=8)
            else:  # "text"
                lbl = ttk.Label(inner, text=block[1], font=UI_FONT)
                lbl.grid(row=row, column=0, columnspan=2, sticky="w", padx=(self.TEXT_INDENT, 0), pady=2)
                self._wide_labels.append((lbl, self.TEXT_INDENT))
            row += 1

    def _on_canvas_configure(self, event):
        # 안쪽 프레임 폭을 캔버스 폭에 맞춰 설명 열이 남는 폭을 쓰게 하고, 그 폭에 맞춰 줄바꿈함
        self._canvas.itemconfigure(self._inner_id, width=event.width)
        self._apply_wrap(event.width)

    def _apply_wrap(self, width):
        # 단축키 열은 가장 긴 단축키 폭(최대 창 폭의 45%)만큼, 나머지는 설명 열이 사용
        key_col = min(self._key_col_width, int(width * 0.45))
        if key_col:
            for lbl in self._key_labels:
                lbl.configure(wraplength=key_col)
        desc_width = max(120, width - key_col - sum(self.KEY_PAD) - 4)
        for lbl in self._desc_labels:
            lbl.configure(wraplength=desc_width)
        for lbl, indent in self._wide_labels:
            lbl.configure(wraplength=max(120, width - indent - 4))

    def _on_mousewheel(self, event):
        if event.delta:
            self._canvas.yview_scroll(-2 if event.delta > 0 else 2, "units")


class ChecklistTab:
    """"체크리스트" 탭: 왼쪽에 폴더(쇼핑리스트/할일 등 분류) 목록, 오른쪽에 선택된
    폴더의 체크리스트 항목([상태|내용]) 목록을 보여줌.

    UI와 조작 방식은 "컬렉션" 탭(CollectionTab)과 같고, 항목이 URL/메모가 아니라
    완료 여부(상태)와 내용만 가진다는 점이 다름:
      - 항목 목록은 [상태(☑/☐)|내용] 2열 고정 (URL 열이 없으므로 컬렉션 같은 반응형 열
        전환이 필요 없음)
      - URL 제목 자동 수집이나 링크 열기 같은 URL 전용 기능은 없음
      - Space는 "완료 여부 토글"임 (컬렉션에서는 편집 창 열기). 내용 수정은 F2/더블클릭
      - 폴더 쪽 동작(추가/이름변경/삭제/순서변경/드래그)과 항목 쪽 동작(추가/삭제/순서변경/
        드래그/인라인편집/포커스 복원)은 컬렉션 탭과 같은 방식임
      - 오른쪽 하단의 [클립보드로 복사]는 선택한 항목을 "[v] 내용"(완료) 또는 "[ ] 내용"
        (미완료) 한 줄로 복사함. 선택한 항목이 없으면 버튼이 비활성화됨
    """

    def __init__(self, parent, app):
        self.app = app
        self.data = app.store.load_checklists()
        if not self.data["folders"]:
            # 최초 실행 등으로 폴더가 하나도 없으면, 컬렉션 탭과 마찬가지로 빈 화면
            # 대신 기본 폴더 하나를 만들어 바로 항목을 추가할 수 있게 함
            self.data["folders"].append(self._make_folder("할 일"))

        self._sash_initialized = False

        # 폴더 목록(왼쪽) 드래그 상태
        self._folder_id_by_index = []
        self._folder_drag_start = None
        self._folder_drag_moved = False

        # 항목 목록(오른쪽) 드래그/클릭 상태
        self._item_drag_id = None
        self._item_drag_moved = False
        self._item_press_col = None  # 누른 시점의 열("status"/"content") - 드래그가 아닌
        # 순수 클릭으로 뗐을 때 상태열이면 체크박스를 바로 토글하는 데 사용

        # 인라인 편집(내용) 상태
        self._inline_editor = None
        self._inline_edit_row_id = None
        # 편집을 "시작한" 폴더 id. 편집 내용은 확정되는 순간 선택된 폴더가 아니라 이 폴더의
        # 항목에 저장해야 함 (_commit_inline_edit 참고)
        self._inline_edit_folder_id = None

        self._current_colors = THEME_COLORS["light"]
        self._content_font = app.settings_mgr.content_font

        main_pane = ttk.PanedWindow(parent, orient=tk.HORIZONTAL)
        main_pane.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        self.main_pane = main_pane

        # ---- 왼쪽: 폴더 목록 ----
        left_panel = ttk.Frame(main_pane)
        main_pane.add(left_panel, weight=0)

        folder_list_frame = ttk.Frame(left_panel)
        folder_list_frame.pack(fill=tk.BOTH, expand=True)
        self.folder_listbox = tk.Listbox(folder_list_frame, exportselection=False,
                                          font=UI_FONT, activestyle="none")
        self.folder_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        folder_scroll = ttk.Scrollbar(folder_list_frame, orient="vertical", command=self.folder_listbox.yview)
        folder_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.folder_listbox.config(yscrollcommand=folder_scroll.set)

        folder_button_frame = ttk.Frame(left_panel)
        folder_button_frame.pack(fill=tk.X, pady=5)
        add_folder_btn = ttk.Button(folder_button_frame, text="추가", command=self._new_folder)
        add_folder_btn.pack(side=tk.LEFT, expand=True, fill=tk.X)
        del_folder_btn = ttk.Button(folder_button_frame, text="제거", command=self._delete_folder)
        del_folder_btn.pack(side=tk.LEFT, expand=True, fill=tk.X)
        up_folder_btn = ttk.Button(folder_button_frame, text="▲", command=lambda: self._move_folder(-1))
        up_folder_btn.pack(side=tk.LEFT, expand=True, fill=tk.X)
        down_folder_btn = ttk.Button(folder_button_frame, text="▼", command=lambda: self._move_folder(1))
        down_folder_btn.pack(side=tk.LEFT, expand=True, fill=tk.X)

        # ---- 오른쪽: 선택된 폴더의 체크리스트 항목 ----
        right_panel = ttk.Frame(main_pane)
        main_pane.add(right_panel, weight=1)

        add_row = ttk.Frame(right_panel)
        add_row.pack(fill=tk.X, pady=(0, 6))
        self.add_entry = ttk.Entry(add_row, font=UI_FONT)
        self.add_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 6))
        bind_when_visible(self.add_entry, "<Return>", self._on_add_submit)
        add_item_btn = ttk.Button(add_row, text="추가", command=self._on_add_submit)
        add_item_btn.pack(side=tk.LEFT)

        items_container = ttk.Frame(right_panel)
        items_container.pack(fill=tk.BOTH, expand=True)
        items_container.rowconfigure(0, weight=1)
        items_container.columnconfigure(0, weight=1)

        style = ttk.Style()
        style.configure("Checklist.Treeview", font=self._content_font,
                         rowheight=max(24, int(self._content_font[1] * 2.4)))

        self.items_tree = ttk.Treeview(
            items_container, columns=("status", "content"),
            show="headings", selectmode="browse", style="Checklist.Treeview",
        )
        self.items_tree.heading("status", text="상태")
        self.items_tree.heading("content", text="내용")
        self.items_tree.column("status", width=56, anchor="center", stretch=False)
        self.items_tree.column("content", width=300, anchor="w", stretch=True)

        items_vsb = ttk.Scrollbar(items_container, orient="vertical", command=self.items_tree.yview)
        self.items_tree.configure(yscrollcommand=items_vsb.set)
        self.items_tree.grid(row=0, column=0, sticky="nsew")
        items_vsb.grid(row=0, column=1, sticky="ns")

        # ---- 오른쪽 하단: [클립보드로 복사] 버튼 ----
        # 일반메모 탭과 같은 배치: 탭 전체 폭의 별도 줄이 아니라 "오른쪽 패널의 맨 아래 줄"로 둠.
        # 그래야 왼쪽 목록의 [추가/제거/▲/▼] 줄과 같은 높이에 나란히 놓여 빈 공간이 생기지 않음.
        # pack(before=items_container): 항목 목록보다 먼저 공간을 받게 해서, 창이 작아져도 버튼이
        # 아니라 항목 목록이 줄어듦. (위젯은 목록 뒤에 만들었으므로 Tab 이동 순서는 마지막임)
        copy_bar = ttk.Frame(right_panel)
        copy_bar.pack(side=tk.BOTTOM, fill=tk.X, pady=5, before=items_container)
        self.copy_button = ttk.Button(copy_bar, text="클립보드로 복사", command=self.app.copy_to_clipboard)
        self.copy_button.pack(side=tk.RIGHT)
        self.copy_status_label = ttk.Label(copy_bar, text="", font=("맑은 고딕", 11, "bold"))
        self.copy_status_label.pack(side=tk.RIGHT, padx=(0, 10))
        self.copy_button.state(["disabled"])  # 선택한 항목이 없는 상태로 시작

        # 우클릭 컨텍스트 메뉴
        self.context_menu = tk.Menu(self.app.root, tearoff=0)
        self.context_menu.add_command(label="완료 토글", command=self._toggle_selected_item)
        self.context_menu.add_command(label="내용 수정", command=self._start_inline_edit_for_selected_item)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="삭제", command=self._delete_selected_item)

        # ---- 이벤트 바인딩 ----
        self.folder_listbox.bind("<<ListboxSelect>>", lambda e: self._refresh_items())
        self.folder_listbox.bind("<ButtonPress-1>", self._on_folder_press, add="+")
        self.folder_listbox.bind("<B1-Motion>", self._on_folder_motion, add="+")
        self.folder_listbox.bind("<ButtonRelease-1>", self._on_folder_release, add="+")
        # 폴더 목록의 키 단축키는 전부 bind_when_visible로 걺: 포커스가 있고 화면에 보일 때만
        # 동작함 (다른 탭으로 전환해도 포커스는 안 보이는 목록에 남아 있어, 가드가 없으면 다른
        # 탭에서 누른 PageUp/Delete가 안 보이는 폴더에 적용됨)
        bind_when_visible(self.folder_listbox, "<Delete>", lambda e: self._delete_folder())
        bind_when_visible(self.folder_listbox, "<Prior>", self._on_folder_page_up)
        bind_when_visible(self.folder_listbox, "<Next>", self._on_folder_page_down)
        # Home/End: 폴더 목록(왼쪽)의 첫/마지막 폴더로 이동
        bind_when_visible(self.folder_listbox, "<Home>", self._on_folder_home)
        bind_when_visible(self.folder_listbox, "<End>", self._on_folder_end)
        self.folder_listbox.bind("<Double-Button-1>", lambda e: self._rename_folder())

        self.items_tree.bind("<Double-1>", self._on_items_tree_double_click)
        self.items_tree.bind("<Button-3>", self._show_context_menu)
        self.items_tree.bind("<Button-2>", self._show_context_menu)
        self.items_tree.bind("<ButtonPress-1>", self._on_item_press, add="+")
        self.items_tree.bind("<B1-Motion>", self._on_item_motion, add="+")
        self.items_tree.bind("<ButtonRelease-1>", self._on_item_release, add="+")
        self.items_tree.bind("<<TreeviewSelect>>", self._on_item_select)
        # 항목 목록의 키 단축키도 전부 bind_when_visible (폴더 목록과 같은 이유)
        bind_when_visible(self.items_tree, "<Delete>", lambda e: self._delete_selected_item())
        bind_when_visible(self.items_tree, "<space>", self._on_item_space)
        bind_when_visible(self.items_tree, "<Prior>", self._on_item_page_up)
        bind_when_visible(self.items_tree, "<Next>", self._on_item_page_down)
        # Home/End: 항목 목록(오른쪽)의 첫/마지막 항목으로 이동 (항목 목록에 포커스가 있을
        # 때만 동작함. 인라인 편집창(Entry)은 items_tree의 자식 위젯이라 이 바인딩을
        # 거치지 않으므로 편집 중의 Home/End는 그대로 편집창 커서 이동임)
        bind_when_visible(self.items_tree, "<Home>", self._on_item_home)
        bind_when_visible(self.items_tree, "<End>", self._on_item_end)

        self._refresh_folders()

    # ==================== 데이터 CRUD ====================

    @staticmethod
    def _make_folder(name):
        return {"id": short_id(), "name": name, "created": now_iso(), "items": []}

    def _get_folder(self, fid):
        for folder in self.data["folders"]:
            if folder["id"] == fid:
                return folder
        return None

    def _add_folder(self, name, after_id=None):
        folder = self._make_folder(name)
        folders = self.data["folders"]
        insert_at = len(folders)
        if after_id:
            idx = next((i for i, f in enumerate(folders) if f["id"] == after_id), None)
            if idx is not None:
                insert_at = idx + 1
        folders.insert(insert_at, folder)
        self.app.save_checklists()
        return folder

    def _rename_folder_data(self, fid, new_name):
        folder = self._get_folder(fid)
        if folder:
            folder["name"] = new_name
            self.app.save_checklists()

    def _delete_folder_data(self, fid):
        self.data["folders"] = [f for f in self.data["folders"] if f["id"] != fid]
        self.app.save_checklists()

    def _reorder_folders_data(self, ordered_ids):
        lookup = {f["id"]: f for f in self.data["folders"]}
        self.data["folders"] = [lookup[i] for i in ordered_ids if i in lookup]
        self.app.save_checklists()

    def _add_item_data(self, fid, content, item_id=None, after_id=None, checked=False):
        folder = self._get_folder(fid)
        if not folder or not content:
            return None
        item = {"id": item_id or short_id(), "content": content, "checked": checked, "added": now_iso()}
        items = folder["items"]
        insert_at = len(items)
        if after_id:
            idx = next((i for i, it in enumerate(items) if it["id"] == after_id), None)
            if idx is not None:
                insert_at = idx + 1
        items.insert(insert_at, item)
        self.app.save_checklists()
        return item

    def _update_item_data(self, fid, item_id, **fields):
        folder = self._get_folder(fid)
        if not folder:
            return
        for item in folder["items"]:
            if item["id"] == item_id:
                for key, value in fields.items():
                    if value is not None:
                        item[key] = value
                self.app.save_checklists()
                return

    def _delete_item_data(self, fid, item_id):
        folder = self._get_folder(fid)
        if not folder:
            return
        folder["items"] = [i for i in folder["items"] if i["id"] != item_id]
        self.app.save_checklists()

    def _reorder_items_data(self, fid, ordered_ids):
        folder = self._get_folder(fid)
        if not folder:
            return
        lookup = {i["id"]: i for i in folder["items"]}
        folder["items"] = [lookup[i] for i in ordered_ids if i in lookup]
        self.app.save_checklists()

    def _find_item(self, fid, item_id):
        folder = self._get_folder(fid)
        if not folder:
            return None
        for item in folder["items"]:
            if item["id"] == item_id:
                return item
        return None

    # ==================== MemoApp이 공통으로 호출하는 인터페이스 ====================

    def set_content_font(self, font_tuple):
        self._content_font = font_tuple
        style = ttk.Style()
        style.configure("Checklist.Treeview", font=font_tuple, rowheight=max(24, int(font_tuple[1] * 2.4)))

    def apply_theme_colors(self, colors):
        self._current_colors = colors
        self.folder_listbox.config(
            bg=colors["bg"], fg=colors["fg"],
            selectbackground=colors["list_select_bg"], selectforeground=colors["list_select_fg"],
            relief=tk.FLAT, borderwidth=0, highlightthickness=1,
            highlightbackground=colors["border"], highlightcolor=colors["accent"],
        )
        # 완료된 항목은 은은하게 흐린 색으로 표시해 미완료 항목과 한눈에 구분되게 함
        self.items_tree.tag_configure("checked", foreground=colors["muted_fg"])

    def get_status_text(self):
        total = len(self.data["folders"])
        fid = self._get_selected_folder_id()
        if fid:
            folder = self._get_folder(fid)
            if folder:
                text = f"총 {total}개의 폴더"
                if fid in self._folder_id_by_index:
                    text += f" 중 {self._folder_id_by_index.index(fid) + 1}번째 선택됨"
                done = sum(1 for it in folder["items"] if it.get("checked"))
                text += f" / 총 {len(folder['items'])}개의 항목 (완료 {done}개)"
                return text
        return f"총 {total}개의 폴더"

    def get_copy_target(self):
        # 선택한 항목이 있을 때만 복사 대상이 있음 ([클립보드로 복사] 버튼의 활성 상태와 같은 조건)
        if not self._get_selected_item_id():
            return None
        return (self._get_copy_text, self.copy_status_label)

    def on_activated(self, event=None):
        if not self._sash_initialized:
            self._sash_initialized = True
            try:
                self.app.root.update_idletasks()
                self.main_pane.sashpos(0, 200)
            except Exception:
                pass

    def on_deactivated(self, event=None):
        self._commit_inline_edit()

    def restore_layout(self):
        """일반메모/컬렉션 탭과 동일한 방식: 창 크기가 바뀌어도 왼쪽(폴더) 패널이
        너무 좁아지지 않도록 사용자가 구분선을 놓을 때마다 최소 폭을 강제함"""
        self.main_pane.bind("<ButtonRelease-1>", lambda e: self._enforce_min_sash())

    def _enforce_min_sash(self):
        try:
            if self.main_pane.sashpos(0) < 200:
                self.main_pane.sashpos(0, 200)
        except Exception:
            pass

    # ==================== 탭 전용/공통 단축키 인터페이스 ====================

    def on_ctrl_n(self, event=None):
        """Ctrl+N: 입력창에 내용이 있으면 그대로 새 항목으로 추가하고, 비어있으면
        입력창에 포커스만 이동함 (컬렉션 탭의 항목 편집 창에 해당하는 것은 없음)"""
        if self.add_entry.get().strip():
            self._on_add_submit()
        else:
            self.focus_primary()
        return "break"

    def on_ctrl_d(self, event=None):
        if self._inline_editor is not None:
            return None
        self._delete_selected_item()
        return "break"

    def on_ctrl_shift_n(self, event=None):
        self._new_folder()
        return "break"

    def focus_content(self, event=None):
        """Ctrl+M: 항목 목록에 포커스"""
        self.items_tree.focus_set()
        children = self.items_tree.get_children()
        if children and not self.items_tree.selection():
            self.items_tree.selection_set(children[0])
            self.items_tree.focus(children[0])
        return "break"

    def focus_primary(self, event=None):
        """Ctrl+T: 항목 추가 입력창으로 이동"""
        self.add_entry.focus_set()
        self.add_entry.select_range(0, tk.END)
        return "break"

    def focus_list(self, event=None):
        """Ctrl+L: 폴더 목록에 포커스"""
        self.folder_listbox.focus_set()
        if not self.folder_listbox.curselection() and self._folder_id_by_index:
            self.folder_listbox.selection_set(0)
            self.folder_listbox.activate(0)
        return "break"

    def on_f2(self, event=None):
        """F2: 항목 목록에 포커스가 있으면 내용 바로 수정, 아니면 폴더 이름 변경"""
        if self._inline_editor is not None:
            return None
        if self.app.root.focus_get() == self.items_tree:
            self._start_inline_edit_for_selected_item()
        else:
            self._rename_folder()
        return "break"

    def insert_text_at_widget(self, widget, text):
        if widget is self.add_entry or (self._inline_editor is not None and widget is self._inline_editor):
            try:
                widget.delete("sel.first", "sel.last")
            except tk.TclError:
                pass
            widget.insert(tk.INSERT, text)
            return True
        return False

    # ==================== 항목 추가 ====================

    def _on_add_submit(self, event=None):
        raw = self.add_entry.get().strip()
        if not raw:
            return "break"
        fid = self._get_selected_folder_id()
        if not fid:
            messagebox.showinfo("폴더 선택", "먼저 왼쪽에서 폴더를 선택하거나 새로 만들어주세요.", parent=self.app.root)
            return "break"
        after_id = self._get_selected_item_id()
        item = self._add_item_data(fid, content=raw, after_id=after_id)
        if item:
            self._update_folder_label(fid)  # 폴더의 항목 수 (N) 갱신 (목록 전체를 다시 그리지 않음)
            self._refresh_items(select_item_id=item["id"])
            self.app.show_status_message("항목을 추가했습니다.")
        self.add_entry.delete(0, tk.END)
        return "break"

    # ==================== 폴더 목록: 조회/렌더링/편집 ====================

    def _get_selected_folder_id(self):
        sel = self.folder_listbox.curselection()
        if not sel:
            return None
        idx = sel[0]
        return self._folder_id_by_index[idx] if 0 <= idx < len(self._folder_id_by_index) else None

    def _refresh_folders(self, select_id=None, select_item_id=None):
        self._commit_inline_edit()
        target_id = select_id or self._get_selected_folder_id()
        ordered_ids = [f["id"] for f in self.data["folders"]]
        select_index = None
        if target_id and target_id in ordered_ids:
            select_index = ordered_ids.index(target_id)
        elif ordered_ids:
            select_index = 0
        self._render_folder_list(ordered_ids, select_index=select_index, select_item_id=select_item_id)

    @staticmethod
    def _folder_label(folder):
        return f"  {folder['name']}  ({len(folder['items'])})"

    def _update_folder_label(self, fid):
        """항목을 추가/삭제해 폴더의 항목 수 표시 (N)만 바뀐 경우, 폴더 목록 전체를 다시
        그리지 않고 그 폴더의 행 글자만 갱신함 (다시 그리면 목록 스크롤이 튐)"""
        folder = self._get_folder(fid)
        if folder and fid in self._folder_id_by_index:
            replace_listbox_row(self.folder_listbox, self._folder_id_by_index.index(fid),
                                self._folder_label(folder))

    def _render_folder_list(self, ordered_ids, select_index=None, select_item_id=None):
        # 다시 그리면 스크롤이 맨 위로 초기화되므로, 보던 위치를 기억해 두었다가 되돌림
        old_ids = self._folder_id_by_index
        old_top = self.folder_listbox.nearest(0) if self.folder_listbox.size() else None
        self.folder_listbox.delete(0, tk.END)
        for fid in ordered_ids:
            folder = self._get_folder(fid)
            if folder:
                self.folder_listbox.insert(tk.END, self._folder_label(folder))
        self._folder_id_by_index = list(ordered_ids)
        restore_listbox_top(self.folder_listbox, old_ids, old_top, self._folder_id_by_index)
        if select_index is not None and 0 <= select_index < len(self._folder_id_by_index):
            self.folder_listbox.selection_set(select_index)
            self.folder_listbox.activate(select_index)
            self.folder_listbox.see(select_index)
        self._refresh_items(select_item_id=select_item_id)

    def _new_folder(self):
        name = simpledialog.askstring("새 폴더", "폴더 이름을 입력하세요:", parent=self.app.root)
        if name and name.strip():
            current_id = self._get_selected_folder_id()
            new_folder = self._add_folder(name.strip(), after_id=current_id)
            self._refresh_folders(select_id=new_folder["id"])
            self.app.show_status_message(f"'{name.strip()}' 폴더를 만들었습니다.")
        # simpledialog(모달 Toplevel)가 닫힌 뒤 포커스가 유실되는 문제 방지 (취소 시에도 동일 적용)
        self.folder_listbox.focus_set()

    def _rename_folder(self):
        fid = self._get_selected_folder_id()
        if not fid:
            messagebox.showinfo("알림", "이름을 변경할 폴더를 선택해주세요.", parent=self.app.root)
            return
        folder = self._get_folder(fid)
        new_name = simpledialog.askstring(
            "폴더 이름 변경", "새 이름을 입력하세요:", initialvalue=folder["name"], parent=self.app.root)
        if new_name and new_name.strip():
            self._rename_folder_data(fid, new_name.strip())
            self._refresh_folders()
        self.folder_listbox.focus_set()

    def _delete_folder(self):
        fid = self._get_selected_folder_id()
        if not fid:
            messagebox.showinfo("알림", "삭제할 폴더를 선택해주세요.", parent=self.app.root)
            return
        folder = self._get_folder(fid)
        count = len(folder["items"])
        if messagebox.askyesno(
            "폴더 삭제",
            f"'{folder['name']}' 폴더와 포함된 항목 {count}개가 모두 삭제됩니다.\n계속하시겠습니까?",
            parent=self.app.root,
        ):
            self._delete_folder_data(fid)
            self._refresh_folders()
            self.app.show_status_message("폴더를 삭제했습니다.")

    def _move_folder(self, direction):
        fid = self._get_selected_folder_id()
        if not fid:
            return
        ids = [f["id"] for f in self.data["folders"]]
        idx = ids.index(fid)
        new_idx = idx + direction
        if not (0 <= new_idx < len(ids)):
            return
        ids[idx], ids[new_idx] = ids[new_idx], ids[idx]
        self._reorder_folders_data(ids)
        self._refresh_folders(select_id=fid)

    def _on_folder_page_up(self, event=None):
        self._move_folder(-1)
        return "break"

    def _on_folder_page_down(self, event=None):
        self._move_folder(1)
        return "break"

    def _on_folder_home(self, event=None):
        focus_listbox_edge(self.folder_listbox, to_end=False)
        return "break"

    def _on_folder_end(self, event=None):
        focus_listbox_edge(self.folder_listbox, to_end=True)
        return "break"

    def _on_folder_press(self, event):
        self._folder_drag_start = self.folder_listbox.nearest(event.y)
        self._folder_drag_moved = False

    def _on_folder_motion(self, event):
        if self._folder_drag_start is None:
            return
        current = self.folder_listbox.nearest(event.y)
        if 0 <= current < self.folder_listbox.size():
            self.folder_listbox.activate(current)
            self._folder_drag_moved = True
        return "break"

    def _on_folder_release(self, event):
        start = self._folder_drag_start
        self._folder_drag_start = None
        moved = self._folder_drag_moved
        self._folder_drag_moved = False
        if start is None or not moved:
            return
        drop = self.folder_listbox.nearest(event.y)
        if not (0 <= drop < len(self._folder_id_by_index)) or drop == start:
            return
        ids = list(self._folder_id_by_index)
        dragged = ids.pop(start)
        ids.insert(drop, dragged)
        self._reorder_folders_data(ids)
        self._refresh_folders(select_id=dragged)

    # ==================== 항목 목록: 조회/렌더링 ====================

    def _get_selected_item_id(self):
        sel = self.items_tree.selection()
        return sel[0] if sel else None

    def _on_item_select(self, event=None):
        self._update_copy_button_state()
        self.app.update_status_bar()

    def _update_copy_button_state(self):
        """[클립보드로 복사] 버튼은 선택한 항목이 있을 때만 누를 수 있음"""
        self.copy_button.state(["!disabled"] if self._get_selected_item_id() else ["disabled"])

    def _get_copy_text(self):
        """선택한 항목을 복사용 문장으로 만듦: 완료면 "[v] 내용", 미완료면 "[ ] 내용".
        (복사하는 순간의 데이터 기준)"""
        fid = self._get_selected_folder_id()
        item_id = self._get_selected_item_id()
        item = self._find_item(fid, item_id) if fid and item_id else None
        if not item:
            return ""
        content = (item.get("content") or "").strip()
        return f"[{'v' if item.get('checked') else ' '}] {content}"

    def _refresh_items(self, select_item_id=None):
        self._commit_inline_edit()
        for row in self.items_tree.get_children():
            self.items_tree.delete(row)
        fid = self._get_selected_folder_id()
        folder = self._get_folder(fid) if fid else None
        if folder:
            for item in folder["items"]:
                checked = bool(item.get("checked"))
                self.items_tree.insert(
                    "", "end", iid=item["id"],
                    values=("☑" if checked else "☐", item.get("content", "")),
                    tags=("checked",) if checked else (),
                )
            if select_item_id and self.items_tree.exists(select_item_id):
                self.items_tree.selection_set(select_item_id)
                self.items_tree.focus(select_item_id)
                self.items_tree.see(select_item_id)
        # 목록을 다시 그리면 선택이 바뀌므로(없어지거나 select_item_id로 복원됨) 버튼 상태도 맞춤
        self._update_copy_button_state()
        self.app.update_status_bar()

    # ==================== 항목 완료 토글 (Space / 상태열 클릭 / 컨텍스트 메뉴) ====================

    def _toggle_item_checked(self, fid, item_id):
        item = self._find_item(fid, item_id)
        if not item:
            return
        self._update_item_data(fid, item_id, checked=not item.get("checked"))
        self._refresh_items(select_item_id=item_id)

    def _toggle_selected_item(self):
        fid = self._get_selected_folder_id()
        item_id = self._get_selected_item_id()
        if fid and item_id:
            self._toggle_item_checked(fid, item_id)

    def _on_item_space(self, event=None):
        self._toggle_selected_item()
        return "break"

    # ==================== 항목 삭제/컨텍스트 메뉴 ====================

    def _delete_selected_item(self):
        fid = self._get_selected_folder_id()
        item_id = self._get_selected_item_id()
        if not fid or not item_id:
            return
        if messagebox.askyesno("항목 삭제", "선택한 항목을 삭제하시겠습니까?", parent=self.app.root):
            self._delete_item_data(fid, item_id)
            # 폴더 목록 전체가 아니라 그 폴더의 항목 수 (N)와 오른쪽 항목 목록만 갱신함
            self._update_folder_label(fid)
            self._refresh_items()
            self.app.show_status_message("항목을 삭제했습니다.")

    def _show_context_menu(self, event):
        row_id = self.items_tree.identify_row(event.y)
        if row_id:
            self.items_tree.selection_set(row_id)
            self.items_tree.focus(row_id)
            self.context_menu.tk_popup(event.x_root, event.y_root)

    # ==================== 항목 드래그(순서 변경) / 클릭(체크박스 토글) ====================

    def _item_column_at(self, event):
        col_id = self.items_tree.identify_column(event.x)
        if col_id == "#1":
            return "status"
        if col_id == "#2":
            return "content"
        return None

    def _on_item_press(self, event):
        self._item_drag_id = self.items_tree.identify_row(event.y)
        self._item_drag_moved = False
        self._item_press_col = self._item_column_at(event)

    def _on_item_motion(self, event):
        if not self._item_drag_id:
            return
        target = self.items_tree.identify_row(event.y)
        if target and target != self._item_drag_id:
            self.items_tree.move(self._item_drag_id, "", self.items_tree.index(target))
            self._item_drag_moved = True

    def _on_item_release(self, event=None):
        drag_id = self._item_drag_id
        self._item_drag_id = None
        moved = self._item_drag_moved
        self._item_drag_moved = False
        press_col = self._item_press_col
        self._item_press_col = None
        if not drag_id:
            return
        if not moved:
            # 드래그 없이 그냥 클릭만 한 경우: "상태" 열을 클릭했다면 체크박스를 바로
            # 토글함 (흔한 체크리스트 UI처럼 클릭 한 번으로 완료 표시가 가능하도록)
            if press_col == "status":
                fid = self._get_selected_folder_id()
                if fid:
                    self._toggle_item_checked(fid, drag_id)
            return
        fid = self._get_selected_folder_id()
        if fid:
            self._reorder_items_data(fid, list(self.items_tree.get_children()))

    def _move_item(self, direction):
        fid = self._get_selected_folder_id()
        item_id = self._get_selected_item_id()
        if not fid or not item_id:
            return
        folder = self._get_folder(fid)
        ids = [i["id"] for i in folder["items"]]
        if item_id not in ids:
            return
        idx = ids.index(item_id)
        new_idx = idx + direction
        if not (0 <= new_idx < len(ids)):
            return
        ids[idx], ids[new_idx] = ids[new_idx], ids[idx]
        self._reorder_items_data(fid, ids)
        self._refresh_items(select_item_id=item_id)

    def _on_item_page_up(self, event=None):
        self._move_item(-1)
        return "break"

    def _on_item_page_down(self, event=None):
        self._move_item(1)
        return "break"

    def _on_item_home(self, event=None):
        focus_tree_edge(self.items_tree, to_end=False)
        return "break"

    def _on_item_end(self, event=None):
        focus_tree_edge(self.items_tree, to_end=True)
        return "break"

    def _on_items_tree_double_click(self, event):
        if self.items_tree.identify_region(event.x, event.y) != "cell":
            return
        row_id = self.items_tree.identify_row(event.y)
        if not row_id:
            return
        col = self._item_column_at(event)
        self.items_tree.selection_set(row_id)
        self.items_tree.focus(row_id)
        if col == "status":
            fid = self._get_selected_folder_id()
            if fid:
                self._toggle_item_checked(fid, row_id)
        else:
            self._begin_inline_edit(row_id)

    # ==================== 항목 내용 인라인 편집 (F2 / 더블클릭 / 컨텍스트 메뉴) ====================

    def _start_inline_edit_for_selected_item(self):
        item_id = self._get_selected_item_id()
        if item_id:
            self._begin_inline_edit(item_id)

    def _begin_inline_edit(self, row_id):
        self._commit_inline_edit()
        if not self.items_tree.exists(row_id):
            return
        self.items_tree.selection_set(row_id)
        self.items_tree.focus(row_id)
        self.items_tree.see(row_id)
        self.items_tree.update_idletasks()
        bbox = self.items_tree.bbox(row_id, "#2")
        if not bbox:
            return
        x, y, width, height = bbox
        fid = self._get_selected_folder_id()
        item = self._find_item(fid, row_id) if fid else None
        current_value = item.get("content", "") if item else self.items_tree.set(row_id, "content")
        colors = self._current_colors
        editor = tk.Entry(
            self.items_tree, font=UI_FONT, relief="solid", borderwidth=1,
            bg=colors["bg"], fg=colors["fg"], insertbackground=colors["insert_bg"],
        )
        editor.insert(0, current_value)
        editor.place(x=x, y=y, width=width, height=height)
        editor.focus_set()
        editor.select_range(0, "end")
        editor.icursor("end")
        self._inline_editor = editor
        self._inline_edit_row_id = row_id
        self._inline_edit_folder_id = fid
        editor.bind("<Return>", lambda e: self._commit_inline_edit())
        editor.bind("<KP_Enter>", lambda e: self._commit_inline_edit())
        editor.bind("<Escape>", lambda e: self._cancel_inline_edit())
        editor.bind("<FocusOut>", lambda e: self._commit_inline_edit())

    def _commit_inline_edit(self):
        if not self._inline_editor or not self._inline_edit_row_id:
            return
        row_id = self._inline_edit_row_id
        # 편집을 시작한 폴더. 편집 중에 다른 폴더를 클릭하면 폴더 선택이 먼저 바뀐 뒤
        # (<<ListboxSelect>> -> _refresh_items) 그 안에서 편집이 확정되므로, 확정 시점의 선택
        # 폴더로 항목을 찾으면 엉뚱한 폴더를 뒤져 편집이 버려짐. 그래서 시작한 폴더 id로 찾음
        edit_fid = self._inline_edit_folder_id
        new_value = self._inline_editor.get().strip()
        editor = self._inline_editor
        # 편집창(Entry)이 사라지기 전, 아직 그 안에 포커스가 있었는지 기억해둠 (컬렉션
        # 탭과 동일한 이유 - Enter로 편집을 마치면 그렇지만, 다른 위젯을 클릭해서
        # FocusOut으로 편집이 끝난 경우엔 이미 포커스가 그쪽으로 옮겨간 뒤이므로 해당 없음)
        editor_had_focus = (self.app.root.focus_get() is editor)
        self._inline_editor = None
        self._inline_edit_row_id = None
        self._inline_edit_folder_id = None
        try:
            editor.destroy()
        except tk.TclError:
            pass
        if editor_had_focus:
            self.items_tree.focus_set()
        if not new_value:
            self.app.show_status_message("내용은 비워둘 수 없어 변경하지 않았습니다.")
            return
        fid = edit_fid or self._get_selected_folder_id()
        if fid and self._find_item(fid, row_id):
            self._update_item_data(fid, row_id, content=new_value)
            # 지금 보고 있는 폴더가 편집한 폴더일 때만 목록을 다시 그림. 다른 폴더로 옮겨가는
            # 중이면(호출한 쪽인 _refresh_items가 곧 새 폴더의 항목으로 다시 그림) 건드리지 않음
            if fid == self._get_selected_folder_id():
                self._refresh_items(select_item_id=row_id)
            self.app.show_status_message("항목을 수정했습니다.")

    def _cancel_inline_edit(self):
        if self._inline_editor:
            editor = self._inline_editor
            self._inline_editor = None
            self._inline_edit_row_id = None
            self._inline_edit_folder_id = None
            try:
                editor.destroy()
            except tk.TclError:
                pass
            self.items_tree.focus_set()

    # ---- 가져오기/내보내기/백업 훅 (일반메모 탭의 같은 절 설명 참고) ----

    transfer_label = "체크리스트"
    transfer_filename = "checklists.json"

    def transfer_parse(self, raw):
        """checklists.json과 같은 {"folders": [...]} 형태인지 검증하고 정규화함
        (잘못되면 TypeError/ValueError). 키가 빠졌으면 컬렉션 탭 가져오기와 같은 방식으로
        기본값을 채우지만, 타입이 틀린 값은 조용히 보정하지 않고 오류로 알림."""
        if not isinstance(raw, dict) or not isinstance(raw.get("folders"), list):
            raise TypeError('데이터가 {"folders": [...]} 형태가 아닙니다.')
        # 항목/폴더 id가 겹치면 새로 만듦 (직접 편집한 파일 대비)
        seen_parents, seen_items = set(), set()
        cleaned = []
        for folder in raw["folders"]:
            if not isinstance(folder, dict):
                raise ValueError("폴더 항목이 딕셔너리가 아닙니다.")
            raw_items = folder.get("items", [])
            if not isinstance(raw_items, list):
                raise ValueError("폴더의 항목 목록이 리스트가 아닙니다.")
            items = []
            for it in raw_items:
                if not isinstance(it, dict):
                    raise ValueError("항목이 딕셔너리가 아닙니다.")
                checked = it.get("checked", False)
                if not isinstance(checked, bool):
                    raise ValueError("항목의 완료 여부(checked)는 true/false여야 합니다.")
                items.append({
                    "id": unique_id(it.get("id"), seen_items),
                    "content": str(it.get("content", "")),
                    "checked": checked,
                    "added": str(it.get("added", "")),
                })
            cleaned.append({
                "id": unique_id(folder.get("id"), seen_parents),
                "name": str(folder.get("name", "이름 없음")),
                "created": str(folder.get("created", "")),
                "items": items,
            })
        return {"folders": cleaned}

    def transfer_summary(self, data):
        folders = data["folders"]
        return f"폴더 {len(folders)}개 (항목 {sum(len(f['items']) for f in folders)}개)"

    def transfer_apply(self, data):
        # 편집 중이던 인라인 편집은 곧 사라질 이전 데이터에 대한 것이므로 커밋하지 않고 버림
        self._cancel_inline_edit()
        self.data = data
        ok = self.app.save_checklists()
        self._refresh_folders()
        return ok

    def transfer_export_json(self):
        return self.data

    def transfer_export_txt(self):
        # 클립보드 복사 양식과 같은 "[v] 내용"/"[ ] 내용" 표기를 폴더별로 묶어 씀
        out = []
        for folder in self.data["folders"]:
            out.append(f"[{folder['name']}]\n")
            for it in folder["items"]:
                out.append(f"{'[v]' if it.get('checked') else '[ ]'} {it.get('content', '')}\n")
            out.append("\n")
        return "".join(out)

    def transfer_export_xlsx(self):
        rows = []
        for folder in self.data["folders"]:
            for it in folder["items"]:
                rows.append([folder["name"], "완료" if it.get("checked") else "미완료", it.get("content", "")])
        return "체크리스트", ["폴더", "상태", "내용"], rows


class CollectionTab:
    """"컬렉션" 탭: 왼쪽 컬렉션(폴더) 목록 + 오른쪽 선택된 컬렉션의 항목(링크/메모) 목록.

    800×600 최소 크기에 맞춘 UI:
      - URL 입력창과 메모 입력창이 하나이며, 입력값이 URL처럼 보이면 링크 항목으로,
        아니면 메모 항목으로 추가함 (Ctrl+N을 누르면 제목/URL/메모를 한 번에 입력하는
        편집 창이 뜸 - 상황에 맞게 선택해서 사용)
      - 항목 목록은 창이 좁으면 [제목/메모] 2열, 넓어지면 [제목/URL/메모] 3열로 자동
        전환됨 (URL이 있는 항목은 좁을 때도 제목 앞에 🔗로 표시)
      - requests가 설치되어 있으면 URL 제목을 자동으로 가져옴 (이미지 첨부는 지원하지 않음)
      - 오른쪽 하단의 [클립보드로 복사]는 선택한 항목을 "제목: ... / URL: ... / 메모: ..."
        세 줄로 복사함. 선택한 항목이 없으면 버튼이 비활성화됨
    """

    # 이 폭(px) 이상일 때만 항목 목록에 URL 열을 함께 표시함 (그보다 좁으면
    # [제목/메모] 2열만 보여줌). 800×600 최소 크기에서 이 컨테이너의 실제 폭은
    # 약 574px이므로, 그보다 확실히 높은 650을 기준으로 잡아 최소 크기에서는
    # 항상 2열이 기본이 되고, 창을 900px 안팎으로 넓히면 3열로 전환되게 함
    URL_COL_MIN_WIDTH = 650

    # 제목 셀 왼쪽부터 이 폭(px)까지를 "🔗 아이콘 위" 로 간주해 URL 풍선말을 띄움.
    # Treeview는 텍스트 중 한 글자만 콕 집어 마우스가 그 위에 있는지 확인하는
    # 기능이 없어, 이모지 한 글자 정도의 폭을 어림잡은 값임
    LINK_ICON_ZONE_WIDTH = 26

    _URL_LIKE_RE = re.compile(r"^[\w.\-]+\.[a-zA-Z]{2,}(/\S*)?$")

    def __init__(self, parent, app):
        self.app = app
        self.data = app.store.load_collections()
        if not self.data["collections"]:
            self.data["collections"].append(self._make_collection("내 컬렉션"))

        self.result_queue = queue.Queue()
        self.fetcher = TitleFetcher(self.result_queue)
        self._pending_fetches = {}
        self._poll_after_id = None
        self._shown_missing_notice = False
        self._sash_initialized = False

        # 컬렉션 목록 상태
        self._collection_id_by_index = []
        self._collection_drag_start = None
        self._collection_drag_moved = False

        # 항목 목록(드래그) 상태
        self._item_drag_id = None
        self._item_drag_moved = False

        # 인라인 편집 상태 (제목 전용 — 메모/URL은 편집 창을 사용)
        self._inline_editor = None
        self._inline_edit_row_id = None
        # 편집을 "시작한" 컬렉션 id. 편집 내용은 확정되는 순간 선택된 컬렉션이 아니라 이
        # 컬렉션의 항목에 저장해야 함 (_commit_inline_edit 참고)
        self._inline_edit_collection_id = None

        # 🔗 아이콘 위에서 보여주는 URL 풍선말 상태
        self._link_tooltip = None
        self._link_tooltip_item_id = None

        self._current_colors = THEME_COLORS["light"]
        self._content_font = app.settings_mgr.content_font
        self._url_col_visible = False

        main_pane = ttk.PanedWindow(parent, orient=tk.HORIZONTAL)
        main_pane.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        self.main_pane = main_pane

        # ---- 왼쪽: 컬렉션(폴더) 목록 ----
        left_panel = ttk.Frame(main_pane)
        main_pane.add(left_panel, weight=0)

        list_frame = ttk.Frame(left_panel)
        list_frame.pack(fill=tk.BOTH, expand=True)
        self.collection_listbox = tk.Listbox(list_frame, exportselection=False, font=UI_FONT, activestyle="none")
        self.collection_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        col_scroll = ttk.Scrollbar(list_frame, orient="vertical", command=self.collection_listbox.yview)
        col_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.collection_listbox.config(yscrollcommand=col_scroll.set)

        button_frame = ttk.Frame(left_panel)
        button_frame.pack(fill=tk.X, pady=5)
        add_col_btn = ttk.Button(button_frame, text="추가", command=self._new_collection)
        add_col_btn.pack(side=tk.LEFT, expand=True, fill=tk.X)
        del_col_btn = ttk.Button(button_frame, text="제거", command=self._delete_collection)
        del_col_btn.pack(side=tk.LEFT, expand=True, fill=tk.X)
        up_col_btn = ttk.Button(button_frame, text="▲", command=lambda: self._move_collection(-1))
        up_col_btn.pack(side=tk.LEFT, expand=True, fill=tk.X)
        down_col_btn = ttk.Button(button_frame, text="▼", command=lambda: self._move_collection(1))
        down_col_btn.pack(side=tk.LEFT, expand=True, fill=tk.X)

        # ---- 오른쪽: 선택된 컬렉션의 항목 목록 ----
        right_panel = ttk.Frame(main_pane)
        main_pane.add(right_panel, weight=1)

        add_row = ttk.Frame(right_panel)
        add_row.pack(fill=tk.X, pady=(0, 6))
        self.add_entry = ttk.Entry(add_row, font=UI_FONT)
        self.add_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 6))
        bind_when_visible(self.add_entry, "<Return>", self._on_add_submit)
        add_btn = ttk.Button(add_row, text="추가", command=self._on_add_submit)
        add_btn.pack(side=tk.LEFT)

        items_container = ttk.Frame(right_panel)
        items_container.pack(fill=tk.BOTH, expand=True)
        items_container.rowconfigure(0, weight=1)
        items_container.columnconfigure(0, weight=1)

        style = ttk.Style()
        style.configure("Collection.Treeview", font=self._content_font,
                         rowheight=max(24, int(self._content_font[1] * 2.4)))

        self.items_tree = ttk.Treeview(
            items_container, columns=("title", "url", "memo"),
            show="headings", selectmode="browse", style="Collection.Treeview",
        )
        self.items_tree.heading("title", text="제목")
        self.items_tree.heading("url", text="URL")
        self.items_tree.heading("memo", text="메모")
        self.items_tree.column("title", width=180, anchor="w", stretch=True)
        self.items_tree.column("url", width=200, anchor="w", stretch=True)
        self.items_tree.column("memo", width=160, anchor="w", stretch=True)
        self.items_tree.configure(displaycolumns=("title", "memo"))

        items_vsb = ttk.Scrollbar(items_container, orient="vertical", command=self.items_tree.yview)
        self.items_tree.configure(yscrollcommand=items_vsb.set)
        self.items_tree.grid(row=0, column=0, sticky="nsew")
        items_vsb.grid(row=0, column=1, sticky="ns")

        # ---- 오른쪽 하단: [클립보드로 복사] 버튼 ----
        # 체크리스트 탭과 같은 배치: 오른쪽 패널의 맨 아래 줄. pack(before=items_container)로
        # 창이 작아져도 버튼이 아니라 항목 목록이 줄어들게 함 (자세한 이유는 ChecklistTab 참고)
        copy_bar = ttk.Frame(right_panel)
        copy_bar.pack(side=tk.BOTTOM, fill=tk.X, pady=5, before=items_container)
        self.copy_button = ttk.Button(copy_bar, text="클립보드로 복사", command=self.app.copy_to_clipboard)
        self.copy_button.pack(side=tk.RIGHT)
        self.copy_status_label = ttk.Label(copy_bar, text="", font=("맑은 고딕", 11, "bold"))
        self.copy_status_label.pack(side=tk.RIGHT, padx=(0, 10))
        self.copy_button.state(["disabled"])  # 선택한 항목이 없는 상태로 시작

        # 컨텍스트 메뉴
        self.context_menu = tk.Menu(self.app.root, tearoff=0)
        self.context_menu.add_command(label="열기", command=self._open_selected_item)
        self.context_menu.add_command(label="편집...", command=self._edit_selected_item)
        self.context_menu.add_command(label="제목 바로 수정", command=self._start_inline_edit_for_selected_item)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="삭제", command=self._delete_selected_item)

        # ---- 이벤트 바인딩 ----
        self.collection_listbox.bind("<<ListboxSelect>>", lambda e: self._refresh_items())
        self.collection_listbox.bind("<ButtonPress-1>", self._on_collection_press, add="+")
        self.collection_listbox.bind("<B1-Motion>", self._on_collection_motion, add="+")
        self.collection_listbox.bind("<ButtonRelease-1>", self._on_collection_release, add="+")
        # 컬렉션 목록의 키 단축키도 전부 bind_when_visible (이유는 ChecklistTab의 폴더 목록과 같음)
        bind_when_visible(self.collection_listbox, "<Delete>", lambda e: self._delete_collection())
        # PageUp/PageDown: 컬렉션 순서 이동. items_tree의 PageUp/PageDown과 마찬가지로
        # 이 위젯에만 직접 바인딩해서, 포커스가 컬렉션 목록에 있을 때는 컬렉션 순서를,
        # 항목 목록에 있을 때는(아래 items_tree 쪽 바인딩) 항목 순서를 바꾸도록 분리함
        bind_when_visible(self.collection_listbox, "<Prior>", self._on_collection_page_up)
        bind_when_visible(self.collection_listbox, "<Next>", self._on_collection_page_down)
        # Home/End: 컬렉션 목록(왼쪽)의 첫/마지막 컬렉션으로 이동
        bind_when_visible(self.collection_listbox, "<Home>", self._on_collection_home)
        bind_when_visible(self.collection_listbox, "<End>", self._on_collection_end)
        self.collection_listbox.bind("<Double-Button-1>", lambda e: self._rename_collection())

        self.items_tree.bind("<Double-1>", self._on_items_tree_double_click)
        self.items_tree.bind("<Button-3>", self._show_context_menu)
        self.items_tree.bind("<Button-2>", self._show_context_menu)
        self.items_tree.bind("<ButtonPress-1>", self._on_item_press, add="+")
        self.items_tree.bind("<B1-Motion>", self._on_item_motion, add="+")
        self.items_tree.bind("<ButtonRelease-1>", self._on_item_release, add="+")
        self.items_tree.bind("<<TreeviewSelect>>", self._on_item_select)
        # 항목 목록의 키 단축키도 전부 bind_when_visible (컬렉션 목록과 같은 이유)
        bind_when_visible(self.items_tree, "<Return>", lambda e: self._open_selected_item())
        bind_when_visible(self.items_tree, "<Delete>", lambda e: self._delete_selected_item())
        bind_when_visible(self.items_tree, "<space>", self._on_item_space)
        # PageUp/PageDown: 항목 순서 이동. 이 위젯에만 직접 바인딩해서, 항목 목록에
        # 포커스가 없을 때는 (컬렉션 탭에는 대응하는 root 차원의 대체 동작이 없어)
        # 아무 일도 일어나지 않게 함 - 다른 탭의 PageUp/PageDown과 서로 간섭하지 않음
        bind_when_visible(self.items_tree, "<Prior>", self._on_item_page_up)
        bind_when_visible(self.items_tree, "<Next>", self._on_item_page_down)
        # Home/End: 항목 목록(오른쪽)의 첫/마지막 항목으로 이동 (제목 인라인 편집창은 자식
        # 위젯이라 이 바인딩을 거치지 않으므로 편집 중의 Home/End는 편집창 커서 이동임)
        bind_when_visible(self.items_tree, "<Home>", self._on_item_home)
        bind_when_visible(self.items_tree, "<End>", self._on_item_end)
        # 제목 앞 🔗 아이콘에 마우스를 올리면 URL을 풍선말로 보여줌
        self.items_tree.bind("<Motion>", self._on_items_tree_motion)
        self.items_tree.bind("<Leave>", lambda e: self._hide_link_tooltip())

        items_container.bind("<Configure>", self._on_items_container_configure)

        self._refresh_collections()
        self._start_polling()


    # ---- 데이터 CRUD (파일 I/O는 app.save_collections()를 통해 즉시 저장) ----

    @staticmethod
    def _make_collection(name):
        return {"id": short_id(), "name": name, "created": now_iso(), "items": []}

    def _get_collection(self, cid):
        for c in self.data["collections"]:
            if c["id"] == cid:
                return c
        return None

    def _add_collection(self, name, after_id=None):
        col = self._make_collection(name)
        collections = self.data["collections"]
        insert_at = len(collections)
        if after_id:
            idx = next((i for i, c in enumerate(collections) if c["id"] == after_id), None)
            if idx is not None:
                insert_at = idx + 1
        collections.insert(insert_at, col)
        self.app.save_collections()
        return col

    def _rename_collection_data(self, cid, new_name):
        col = self._get_collection(cid)
        if col:
            col["name"] = new_name
            self.app.save_collections()

    def _delete_collection_data(self, cid):
        self.data["collections"] = [c for c in self.data["collections"] if c["id"] != cid]
        self.app.save_collections()

    def _reorder_collections_data(self, ordered_ids):
        lookup = {c["id"]: c for c in self.data["collections"]}
        self.data["collections"] = [lookup[i] for i in ordered_ids if i in lookup]
        self.app.save_collections()

    def _add_item_data(self, cid, title, url, memo="", item_id=None, after_id=None):
        col = self._get_collection(cid)
        if not col:
            return None
        if not title and not url and not memo:
            # 제목·URL·메모가 모두 비어있는 항목은 만들지 않음 (호출부에서도 사전 검증됨)
            return None
        item = {
            "id": item_id or short_id(),
            "title": title or url,
            "url": url,
            "memo": memo,
            "added": now_iso(),
        }
        items = col["items"]
        insert_at = len(items)
        if after_id:
            idx = next((i for i, it in enumerate(items) if it["id"] == after_id), None)
            if idx is not None:
                insert_at = idx + 1
        items.insert(insert_at, item)
        self.app.save_collections()
        return item

    def _update_item_data(self, cid, item_id, **fields):
        col = self._get_collection(cid)
        if not col:
            return
        for item in col["items"]:
            if item["id"] == item_id:
                for key, value in fields.items():
                    if value is not None:
                        item[key] = value
                self.app.save_collections()
                return

    def _delete_item_data(self, cid, item_id):
        col = self._get_collection(cid)
        if not col:
            return
        col["items"] = [i for i in col["items"] if i["id"] != item_id]
        self.app.save_collections()

    def _reorder_items_data(self, cid, ordered_ids):
        col = self._get_collection(cid)
        if not col:
            return
        lookup = {i["id"]: i for i in col["items"]}
        col["items"] = [lookup[i] for i in ordered_ids if i in lookup]
        self.app.save_collections()

    def _find_item(self, cid, item_id):
        col = self._get_collection(cid)
        if not col:
            return None
        for item in col["items"]:
            if item["id"] == item_id:
                return item
        return None

    # ---- MemoApp이 공통으로 호출하는 인터페이스 ----

    def set_content_font(self, font_tuple):
        self._content_font = font_tuple
        style = ttk.Style()
        style.configure("Collection.Treeview", font=font_tuple, rowheight=max(24, int(font_tuple[1] * 2.4)))

    def apply_theme_colors(self, colors):
        self._current_colors = colors
        self.collection_listbox.config(
            bg=colors["bg"], fg=colors["fg"],
            selectbackground=colors["list_select_bg"], selectforeground=colors["list_select_fg"],
            relief=tk.FLAT, borderwidth=0, highlightthickness=1,
            highlightbackground=colors["border"], highlightcolor=colors["accent"],
        )

    def get_status_text(self):
        total = len(self.data["collections"])
        cid = self._get_selected_collection_id()
        if cid:
            col = self._get_collection(cid)
            if col:
                text = f"총 {total}개의 컬렉션"
                if cid in self._collection_id_by_index:
                    idx = self._collection_id_by_index.index(cid)
                    text += f" 중 {idx + 1}번째 선택됨"
                text += f" / 총 {len(col['items'])}개의 항목"
                item_id = self._get_selected_item_id()
                if item_id:
                    item = self._find_item(cid, item_id)
                    if item and item.get("url"):
                        text += f" · {item['url']}"
                return text
        return f"총 {total}개의 컬렉션"

    def get_copy_target(self):
        # 컬렉션 탭에는 (일반메모/달력메모와 달리) "현재 내용 편집창"이 없으므로, 선택한 항목을
        # 문장으로 만드는 함수가 복사 대상임. 선택한 항목이 없으면 복사 대상도 없음
        # ([클립보드로 복사] 버튼의 활성 상태와 같은 조건)
        if not self._get_selected_item_id():
            return None
        return (self._get_copy_text, self.copy_status_label)

    def on_activated(self, event=None):
        if not self._sash_initialized:
            # 탭이 실제로 화면에 처음 보이는 시점에 sash 위치를 잡음. 창 시작 시
            # (restore_window_geometry)에는 이 탭이 아직 숨겨진 노트북 페이지라 크기가 확정되지
            # 않아 sashpos()가 반영되지 않고 왼쪽 패널이 0px 가까이로 무너짐 (최소 크기에서 URL
            # 열이 숨겨져야 할 때도 보이는 원인이 됨)
            self._sash_initialized = True
            try:
                self.app.root.update_idletasks()
                self.main_pane.sashpos(0, 200)
            except Exception:
                pass
        if not self._shown_missing_notice and requests is None:
            self._shown_missing_notice = True
            self.app.show_status_message(
                "참고: requests 라이브러리가 없어 URL 제목 자동 가져오기가 비활성화되어 있습니다.",
                duration_ms=6000,
            )

    def on_deactivated(self, event=None):
        # 인라인 제목 편집 중에 다른 탭으로 전환해도 입력한 내용이 사라지지 않도록 커밋함
        self._commit_inline_edit()
        self._hide_link_tooltip()

    def restore_layout(self):
        self.main_pane.bind("<ButtonRelease-1>", lambda e: self._enforce_min_sash())

    def _enforce_min_sash(self):
        # 일반메모 탭(GeneralMemoTab.enforce_min_sash)과 같은 값. 추가/제거/▲/▼
        # 버튼 4개의 실제 필요 폭이 두 탭에서 동일(174px)해서 같은 여유(200px)를 둠
        try:
            if self.main_pane.sashpos(0) < 200:
                self.main_pane.sashpos(0, 200)
        except Exception:
            pass

    # ---- 탭 전용/공통 단축키 인터페이스 (MemoApp이 활성 탭에 위임함) ----

    def on_ctrl_n(self, event=None):
        """Ctrl+N: 제목/URL/메모를 한 번에 입력하는 편집 창을 새 항목으로 엶.
        (입력창에 타이핑하고 Enter/추가 버튼을 누르는 빠른 방법과 별개로, 여러 필드를 한 번에
        채우고 싶을 때 쓰는 경로임. 새 컬렉션은 Ctrl+Shift+N)"""
        cid = self._get_selected_collection_id()
        if not cid:
            messagebox.showinfo("컬렉션 선택", "먼저 왼쪽에서 컬렉션을 선택하거나 새로 만들어주세요.", parent=self.app.root)
            return "break"
        new_id = short_id()
        after_id = self._get_selected_item_id()

        def on_save(title, url, memo):
            created = self._add_item_data(cid, title=title, url=url, memo=memo, item_id=new_id, after_id=after_id)
            if created:
                self._update_collection_label(cid)  # 컬렉션의 항목 수 (N)만 갱신 (목록 전체를 다시 그리지 않음)
                self._refresh_items(select_item_id=new_id)
            self.app.show_status_message("항목을 추가했습니다." if created else "추가를 취소했습니다.")

        EditItemDialog(self.app.root, {"id": new_id, "title": "", "url": "", "memo": ""},
                        on_save, self._content_font, self._current_colors)
        return "break"

    def on_ctrl_d(self, event=None):
        if self._inline_editor is not None:
            return None
        self._delete_selected_item()
        return "break"

    def on_ctrl_shift_n(self, event=None):
        self._new_collection()
        return "break"

    def focus_content(self, event=None):
        """Ctrl+M: 항목 목록에 포커스"""
        self.items_tree.focus_set()
        children = self.items_tree.get_children()
        if children and not self.items_tree.selection():
            self.items_tree.selection_set(children[0])
            self.items_tree.focus(children[0])
        return "break"

    def focus_primary(self, event=None):
        """Ctrl+T: 항목 추가 입력창으로 이동"""
        self.add_entry.focus_set()
        self.add_entry.select_range(0, tk.END)
        return "break"

    def focus_list(self, event=None):
        """Ctrl+L: 컬렉션(폴더) 목록에 포커스"""
        self.collection_listbox.focus_set()
        if not self.collection_listbox.curselection() and self._collection_id_by_index:
            self.collection_listbox.selection_set(0)
            self.collection_listbox.activate(0)
        return "break"

    def on_f2(self, event=None):
        """F2: 항목 목록에 포커스가 있으면 제목 바로 수정, 아니면 컬렉션 이름 변경"""
        if self._inline_editor is not None:
            return None
        if self.app.root.focus_get() == self.items_tree:
            self._start_inline_edit_for_selected_item()
        else:
            self._rename_collection()
        return "break"

    def insert_text_at_widget(self, widget, text):
        if widget is self.add_entry:
            try:
                widget.delete("sel.first", "sel.last")
            except tk.TclError:
                pass
            widget.insert(tk.INSERT, text)
            return True
        if self._inline_editor is not None and widget is self._inline_editor:
            try:
                widget.delete("sel.first", "sel.last")
            except tk.TclError:
                pass
            widget.insert(tk.INSERT, text)
            return True
        return False

    # ---- 항목 추가 (입력창 하나로 URL/메모 자동 판별) ----

    def _looks_like_url(self, text):
        text = text.strip()
        if not text or " " in text or "\t" in text or "\n" in text:
            return False
        lowered = text.lower()
        if lowered.startswith(("http://", "https://", "www.")):
            return True
        return bool(self._URL_LIKE_RE.match(text))

    def _on_add_submit(self, event=None):
        raw = self.add_entry.get().strip()
        if not raw:
            return "break"
        cid = self._get_selected_collection_id()
        if not cid:
            messagebox.showinfo("컬렉션 선택", "먼저 왼쪽에서 컬렉션을 선택하거나 새로 만들어주세요.", parent=self.app.root)
            return "break"
        if self._looks_like_url(raw):
            self._add_item_from_url(raw)
        else:
            after_id = self._get_selected_item_id()
            item = self._add_item_data(cid, title=raw, url="", memo="", after_id=after_id)
            if item:
                self._update_collection_label(cid)
                self._refresh_items(select_item_id=item["id"])
                self.app.show_status_message("메모를 추가했습니다.")
        self.add_entry.delete(0, tk.END)
        return "break"

    def _add_item_from_url(self, raw_url):
        cid = self._get_selected_collection_id()
        if not cid:
            return
        url = normalize_url(raw_url)
        if not url:
            return
        after_id = self._get_selected_item_id()
        item = self._add_item_data(cid, title=url, url=url, memo="", after_id=after_id)
        if not item:
            return
        self._update_collection_label(cid)
        self._refresh_items(select_item_id=item["id"])
        request_id = item["id"]
        self._pending_fetches[request_id] = cid
        self.app.show_status_message(f"제목을 가져오는 중입니다... ({url})")
        self.fetcher.fetch_async(url, request_id)
        self._start_polling()

    # ---- 백그라운드 제목 수집 결과 폴링 ----

    def _start_polling(self):
        if self._poll_after_id is None:
            self._poll_after_id = self.app.root.after(150, self._poll_queue)

    def _stop_polling(self):
        if self._poll_after_id is not None:
            try:
                self.app.root.after_cancel(self._poll_after_id)
            except Exception:
                pass
            self._poll_after_id = None

    def _poll_queue(self):
        self._poll_after_id = None
        try:
            while True:
                msg = self.result_queue.get_nowait()
                request_id = msg.get("request_id")
                cid = self._pending_fetches.pop(request_id, None)
                if cid is None:
                    continue
                item = self._find_item(cid, request_id)
                if item is None:
                    continue
                if msg.get("title"):
                    self._update_item_data(cid, request_id, title=msg["title"])
                    # 목록 전체를 다시 그리면 보고 있던 항목의 선택이 풀리고, 편집 중이던
                    # 인라인 편집이 강제로 확정되므로 그 항목의 행만 갱신함
                    self._update_item_row(cid, request_id)
                    self.app.show_status_message(f"제목을 가져왔습니다: {msg['title']}")
                elif msg.get("error"):
                    self.app.show_status_message(f"제목 가져오기 실패: {msg['error']}")
        except queue.Empty:
            pass
        # 대기 중인 요청이 남아있는 동안만 폴링을 이어감 (없으면 멈춰서 불필요한
        # after() 반복 호출을 줄임 - 새 URL을 추가하는 순간 _start_polling()이 다시 켬)
        if self._pending_fetches:
            self._poll_after_id = self.app.root.after(150, self._poll_queue)

    # ---- 컬렉션 목록: 조회/렌더링 ----

    def _get_selected_collection_id(self):
        sel = self.collection_listbox.curselection()
        if not sel:
            return None
        idx = sel[0]
        if 0 <= idx < len(self._collection_id_by_index):
            return self._collection_id_by_index[idx]
        return None

    def _refresh_collections(self, select_id=None, select_item_id=None):
        self._commit_inline_edit()
        target_id = select_id or self._get_selected_collection_id()
        ordered_ids = [c["id"] for c in self.data["collections"]]
        select_index = None
        if target_id and target_id in ordered_ids:
            select_index = ordered_ids.index(target_id)
        elif ordered_ids:
            select_index = 0
        self._render_collection_list(ordered_ids, select_index=select_index, select_item_id=select_item_id)

    @staticmethod
    def _collection_label(col):
        return f"  {col['name']}  ({len(col['items'])})"

    def _update_collection_label(self, cid):
        """항목을 추가/삭제해 컬렉션의 항목 수 표시 (N)만 바뀐 경우, 컬렉션 목록 전체를 다시
        그리지 않고 그 컬렉션의 행 글자만 갱신함 (다시 그리면 목록 스크롤이 튐)"""
        col = self._get_collection(cid)
        if col and cid in self._collection_id_by_index:
            replace_listbox_row(self.collection_listbox, self._collection_id_by_index.index(cid),
                                self._collection_label(col))

    def _render_collection_list(self, ordered_ids, select_index=None, select_item_id=None):
        # 다시 그리면 스크롤이 맨 위로 초기화되므로, 보던 위치를 기억해 두었다가 되돌림
        old_ids = self._collection_id_by_index
        old_top = self.collection_listbox.nearest(0) if self.collection_listbox.size() else None
        self.collection_listbox.delete(0, tk.END)
        for cid in ordered_ids:
            col = self._get_collection(cid)
            if not col:
                continue
            self.collection_listbox.insert(tk.END, self._collection_label(col))
        self._collection_id_by_index = list(ordered_ids)
        restore_listbox_top(self.collection_listbox, old_ids, old_top, self._collection_id_by_index)
        if select_index is not None and 0 <= select_index < len(self._collection_id_by_index):
            self.collection_listbox.selection_set(select_index)
            # selection_set()은 선택 표시만 하고 방향키 탐색 기준인 "활성(active)" 인덱스는 바꾸지
            # 않으므로, 이 호출이 없으면 PageUp/PageDown으로 순서를 바꾼 뒤 방향키가 0번째 근처로 튐
            self.collection_listbox.activate(select_index)
            self.collection_listbox.see(select_index)
        self._refresh_items(select_item_id=select_item_id)

    def _new_collection(self):
        name = simpledialog.askstring("새 컬렉션", "컬렉션 이름을 입력하세요:", parent=self.app.root)
        if name and name.strip():
            current_id = self._get_selected_collection_id()
            new_col = self._add_collection(name.strip(), after_id=current_id)
            self._refresh_collections(select_id=new_col["id"])
            self.app.show_status_message(f"'{name.strip()}' 컬렉션을 만들었습니다.")
        # simpledialog(모달 Toplevel)가 닫힌 뒤에는 키보드 포커스가 돌아오지 않아 방향키로 목록을
        # 탐색할 수 없으므로 목록에 포커스를 명시적으로 되돌림 (취소했을 때도 동일)
        self.collection_listbox.focus_set()

    def _rename_collection(self):
        cid = self._get_selected_collection_id()
        if not cid:
            messagebox.showinfo("알림", "이름을 변경할 컬렉션을 선택해주세요.", parent=self.app.root)
            return
        col = self._get_collection(cid)
        new_name = simpledialog.askstring(
            "컬렉션 이름 변경", "새 이름을 입력하세요:", initialvalue=col["name"], parent=self.app.root)
        if new_name and new_name.strip():
            self._rename_collection_data(cid, new_name.strip())
            self._refresh_collections()
        # simpledialog가 닫힌 뒤 포커스가 유실되지 않도록 목록에 되돌림
        # (F2로 이름 변경한 뒤 바로 위/아래로 다른 컬렉션을 탐색할 수 있어야 함)
        self.collection_listbox.focus_set()

    def _delete_collection(self):
        cid = self._get_selected_collection_id()
        if not cid:
            messagebox.showinfo("알림", "삭제할 컬렉션을 선택해주세요.", parent=self.app.root)
            return
        col = self._get_collection(cid)
        count = len(col["items"])
        if messagebox.askyesno(
            "컬렉션 삭제",
            f"'{col['name']}' 컬렉션과 포함된 항목 {count}개가 모두 삭제됩니다.\n계속하시겠습니까?",
            parent=self.app.root,
        ):
            self._delete_collection_data(cid)
            self._refresh_collections()
            self.app.show_status_message("컬렉션을 삭제했습니다.")

    def _move_collection(self, direction):
        cid = self._get_selected_collection_id()
        if not cid:
            return
        ids = [c["id"] for c in self.data["collections"]]
        idx = ids.index(cid)
        new_idx = idx + direction
        if not (0 <= new_idx < len(ids)):
            return
        ids[idx], ids[new_idx] = ids[new_idx], ids[idx]
        self._reorder_collections_data(ids)
        self._refresh_collections(select_id=cid)

    def _on_collection_page_up(self, event=None):
        self._move_collection(-1)
        return "break"

    def _on_collection_page_down(self, event=None):
        self._move_collection(1)
        return "break"

    def _on_collection_home(self, event=None):
        focus_listbox_edge(self.collection_listbox, to_end=False)
        return "break"

    def _on_collection_end(self, event=None):
        focus_listbox_edge(self.collection_listbox, to_end=True)
        return "break"

    def _on_collection_press(self, event):
        self._collection_drag_start = self.collection_listbox.nearest(event.y)
        self._collection_drag_moved = False

    def _on_collection_motion(self, event):
        if self._collection_drag_start is None:
            return
        current = self.collection_listbox.nearest(event.y)
        if 0 <= current < self.collection_listbox.size():
            self.collection_listbox.activate(current)
            self._collection_drag_moved = True
        return "break"

    def _on_collection_release(self, event):
        start = self._collection_drag_start
        self._collection_drag_start = None
        if start is None or not self._collection_drag_moved:
            self._collection_drag_moved = False
            return
        self._collection_drag_moved = False
        drop = self.collection_listbox.nearest(event.y)
        if not (0 <= drop < len(self._collection_id_by_index)) or drop == start:
            return
        ids = list(self._collection_id_by_index)
        moved = ids.pop(start)
        ids.insert(drop, moved)
        self._reorder_collections_data(ids)
        self._refresh_collections(select_id=moved)

    # ---- 항목 목록: 조회/렌더링 ----

    def _get_selected_item_id(self):
        sel = self.items_tree.selection()
        return sel[0] if sel else None

    def _on_item_select(self, event=None):
        self._update_copy_button_state()
        self.app.update_status_bar()

    def _update_copy_button_state(self):
        """[클립보드로 복사] 버튼은 선택한 항목이 있을 때만 누를 수 있음"""
        self.copy_button.state(["!disabled"] if self._get_selected_item_id() else ["disabled"])

    def _get_copy_text(self):
        """선택한 항목을 복사용 문장(세 줄)으로 만듦:
            제목: {제목}
            URL: {URL}
            메모: {메모}
        값이 비어 있어도 줄은 그대로 두되 줄 끝에 공백이 남지 않게 "URL:"처럼 씀. 값 앞뒤의
        공백/줄바꿈은 정리하고, 메모 안의 줄바꿈은 그대로 둠. (복사하는 순간의 데이터 기준)"""
        cid = self._get_selected_collection_id()
        item_id = self._get_selected_item_id()
        item = self._find_item(cid, item_id) if cid and item_id else None
        if not item:
            return ""

        def line(label, value):
            value = (value or "").strip()
            return f"{label}: {value}" if value else f"{label}:"

        return "\n".join((line("제목", item.get("title")), line("URL", item.get("url")),
                          line("메모", item.get("memo"))))

    @staticmethod
    def _item_row_values(item):
        """항목 목록(Treeview)의 한 행에 표시할 (제목, URL, 메모 미리보기)"""
        memo_preview = (item.get("memo") or "").replace("\n", " ").strip()
        if len(memo_preview) > 50:
            memo_preview = memo_preview[:50] + "…"
        title_display = item.get("title", "")
        if item.get("url"):
            title_display = f"🔗 {title_display}" if title_display else f"🔗 {item['url']}"
        return (title_display, item.get("url", ""), memo_preview)

    def _update_item_row(self, cid, item_id):
        """지금 보고 있는 컬렉션의 항목 하나의 표시만 새 데이터로 바꿈 (목록을 다시 그리지
        않으므로 선택/스크롤/편집 중인 인라인 편집이 그대로 유지됨)"""
        if cid != self._get_selected_collection_id() or not self.items_tree.exists(item_id):
            return
        item = self._find_item(cid, item_id)
        if item:
            self.items_tree.item(item_id, values=self._item_row_values(item))

    def _refresh_items(self, select_item_id=None):
        self._commit_inline_edit()
        self._hide_link_tooltip()
        for row in self.items_tree.get_children():
            self.items_tree.delete(row)
        cid = self._get_selected_collection_id()
        col = self._get_collection(cid) if cid else None
        if col:
            for item in col["items"]:
                self.items_tree.insert("", "end", iid=item["id"], values=self._item_row_values(item))
            if select_item_id and self.items_tree.exists(select_item_id):
                self.items_tree.selection_set(select_item_id)
                # selection_set()만으로는 방향키 탐색 기준인 "포커스(focus)" 항목이 바뀌지 않으므로
                # focus()도 지정함 (Listbox의 activate()에 대응하는 Treeview의 개념)
                self.items_tree.focus(select_item_id)
                self.items_tree.see(select_item_id)
        # 목록을 다시 그리면 선택이 바뀌므로(없어지거나 select_item_id로 복원됨) 버튼 상태도 맞춤
        self._update_copy_button_state()
        self.app.update_status_bar()

    def _on_items_container_configure(self, event):
        show_url = event.width >= self.URL_COL_MIN_WIDTH
        if show_url != self._url_col_visible:
            self._url_col_visible = show_url
            cols = ("title", "url", "memo") if show_url else ("title", "memo")
            self.items_tree.configure(displaycolumns=cols)

    # ---- 🔗 아이콘 위 URL 풍선말 ----

    def _on_items_tree_motion(self, event):
        """마우스가 제목 칸의 🔗 아이콘 위(칸 왼쪽 끝부터 LINK_ICON_ZONE_WIDTH px 이내)에
        있으면 그 항목의 URL을 풍선말로 보여주고, 아니면 떠 있던 풍선말을 닫음."""
        show_here = False
        row_id = self.items_tree.identify_row(event.y)
        if row_id:
            column_id = self.items_tree.identify_column(event.x)
            displayed = self.items_tree.cget("displaycolumns")
            try:
                col_index = int(str(column_id).replace("#", "")) - 1
            except ValueError:
                col_index = -1
            if 0 <= col_index < len(displayed) and displayed[col_index] == "title":
                cid = self._get_selected_collection_id()
                item = self._find_item(cid, row_id) if cid else None
                if item and item.get("url"):
                    bbox = self.items_tree.bbox(row_id, "title")
                    if bbox and (event.x - bbox[0]) <= self.LINK_ICON_ZONE_WIDTH:
                        show_here = True
                        if self._link_tooltip_item_id != row_id:
                            self._show_link_tooltip(event, item["url"])
                            self._link_tooltip_item_id = row_id
        if not show_here:
            self._hide_link_tooltip()

    def _show_link_tooltip(self, event, url):
        self._hide_link_tooltip()
        tooltip = tk.Toplevel(self.app.root)
        tooltip.wm_overrideredirect(True)
        try:
            tooltip.wm_attributes("-topmost", True)
        except tk.TclError:
            pass
        tooltip.wm_geometry(f"+{event.x_root + 12}+{event.y_root + 12}")
        tk.Label(
            tooltip, text=url, background="#ffffe0", foreground="#000000",
            relief=tk.SOLID, borderwidth=1, font=("맑은 고딕", 9), padx=6, pady=3,
        ).pack()
        self._link_tooltip = tooltip

    def _hide_link_tooltip(self, event=None):
        if self._link_tooltip is not None:
            try:
                self._link_tooltip.destroy()
            except tk.TclError:
                pass
            self._link_tooltip = None
        self._link_tooltip_item_id = None

    def _open_selected_item(self):
        cid = self._get_selected_collection_id()
        item_id = self._get_selected_item_id()
        if not cid or not item_id:
            return
        item = self._find_item(cid, item_id)
        if not item:
            return
        url = item.get("url")
        if not url:
            self.app.show_status_message("메모 항목에는 열 수 있는 링크가 없습니다.")
            return
        if not is_web_url(url):
            self.app.show_status_message("http/https 웹 주소만 열 수 있습니다. 항목 편집에서 URL을 확인해 주세요.")
            return
        try:
            opened = webbrowser.open(url.strip())
        except Exception:
            opened = False
        if not opened:
            self.app.show_status_message("웹 브라우저를 열지 못했습니다.")

    def _edit_selected_item(self):
        cid = self._get_selected_collection_id()
        item_id = self._get_selected_item_id()
        if not cid or not item_id:
            messagebox.showinfo("알림", "편집할 항목을 선택해주세요.", parent=self.app.root)
            return
        item = self._find_item(cid, item_id)
        if not item:
            return

        def on_save(title, url, memo):
            self._update_item_data(cid, item_id, title=title, url=url, memo=memo)
            self._refresh_items(select_item_id=item_id)  # 저장한 항목의 선택을 유지
            self.app.show_status_message("항목을 수정했습니다.")

        EditItemDialog(self.app.root, item, on_save, self._content_font, self._current_colors)

    def _delete_selected_item(self):
        cid = self._get_selected_collection_id()
        item_id = self._get_selected_item_id()
        if not cid or not item_id:
            return
        if messagebox.askyesno("항목 삭제", "선택한 항목을 삭제하시겠습니까?", parent=self.app.root):
            self._delete_item_data(cid, item_id)
            # 컬렉션 목록 전체가 아니라 그 컬렉션의 항목 수 (N)와 오른쪽 항목 목록만 갱신함
            self._update_collection_label(cid)
            self._refresh_items()
            self.app.show_status_message("항목을 삭제했습니다.")

    def _show_context_menu(self, event):
        iid = self.items_tree.identify_row(event.y)
        if iid:
            self.items_tree.selection_set(iid)
            self.items_tree.focus(iid)
            self.context_menu.tk_popup(event.x_root, event.y_root)

    def _on_item_press(self, event):
        self._item_drag_id = self.items_tree.identify_row(event.y)
        self._item_drag_moved = False

    def _on_item_motion(self, event):
        if not self._item_drag_id:
            return
        target = self.items_tree.identify_row(event.y)
        if target and target != self._item_drag_id:
            self.items_tree.move(self._item_drag_id, "", self.items_tree.index(target))
            self._item_drag_moved = True

    def _on_item_release(self, event=None):
        drag_id = self._item_drag_id
        self._item_drag_id = None
        if not drag_id or not self._item_drag_moved:
            self._item_drag_moved = False
            return
        self._item_drag_moved = False
        cid = self._get_selected_collection_id()
        if not cid:
            return
        self._reorder_items_data(cid, list(self.items_tree.get_children()))

    def _move_item(self, direction):
        cid = self._get_selected_collection_id()
        item_id = self._get_selected_item_id()
        if not cid or not item_id:
            return
        col = self._get_collection(cid)
        if not col:
            return
        ids = [i["id"] for i in col["items"]]
        if item_id not in ids:
            return
        idx = ids.index(item_id)
        new_idx = idx + direction
        if not (0 <= new_idx < len(ids)):
            return
        ids[idx], ids[new_idx] = ids[new_idx], ids[idx]
        self._reorder_items_data(cid, ids)
        self._refresh_items(select_item_id=item_id)

    def _on_item_page_up(self, event=None):
        self._move_item(-1)
        return "break"

    def _on_item_page_down(self, event=None):
        self._move_item(1)
        return "break"

    def _on_item_home(self, event=None):
        focus_tree_edge(self.items_tree, to_end=False)
        return "break"

    def _on_item_end(self, event=None):
        focus_tree_edge(self.items_tree, to_end=True)
        return "break"

    def _on_item_space(self, event=None):
        self._edit_selected_item()
        return "break"

    # ---- 항목 더블클릭 (URL 열이 숨겨져 있어도 동작하도록, 열 종류에 따라 분기) ----

    def _on_items_tree_double_click(self, event):
        region = self.items_tree.identify_region(event.x, event.y)
        if region != "cell":
            return
        row_id = self.items_tree.identify_row(event.y)
        column_id = self.items_tree.identify_column(event.x)
        if not row_id:
            return
        displayed = self.items_tree.cget("displaycolumns")
        try:
            col_index = int(str(column_id).replace("#", "")) - 1
        except ValueError:
            return
        if col_index < 0 or col_index >= len(displayed):
            return
        self._handle_item_double_click(row_id, displayed[col_index])

    def _handle_item_double_click(self, row_id, col_key):
        cid = self._get_selected_collection_id()
        item = self._find_item(cid, row_id) if cid else None
        self.items_tree.selection_set(row_id)
        self.items_tree.focus(row_id)
        if col_key == "url":
            self._open_selected_item()
        elif col_key == "title":
            # URL이 있는 항목은 열기가 더 자주 필요한 동작이라 더블클릭=열기로 두고,
            # 제목만 있는 메모 항목은 더블클릭=편집으로 함 (제목만 바꾸고 싶을 땐 F2)
            if item and item.get("url"):
                self._open_selected_item()
            else:
                self._edit_selected_item()
        elif col_key == "memo":
            self._edit_selected_item()

    # ---- 항목 제목 인라인 편집 (F2 / 컨텍스트 메뉴) ----

    def _start_inline_edit_for_selected_item(self):
        item_id = self._get_selected_item_id()
        if item_id:
            self._begin_inline_edit(item_id)

    def _begin_inline_edit(self, row_id):
        self._commit_inline_edit()
        if not self.items_tree.exists(row_id):
            return
        self.items_tree.selection_set(row_id)
        self.items_tree.focus(row_id)
        self.items_tree.see(row_id)
        self.items_tree.update_idletasks()
        bbox = self.items_tree.bbox(row_id, "#1")
        if not bbox:
            return
        x, y, width, height = bbox
        cid = self._get_selected_collection_id()
        item = self._find_item(cid, row_id) if cid else None
        current_value = item.get("title", "") if item else self.items_tree.set(row_id, "title")
        colors = self._current_colors
        editor = tk.Entry(
            self.items_tree, font=UI_FONT, relief="solid", borderwidth=1,
            bg=colors["bg"], fg=colors["fg"], insertbackground=colors["insert_bg"],
        )
        editor.insert(0, current_value)
        editor.place(x=x, y=y, width=width, height=height)
        editor.focus_set()
        editor.select_range(0, "end")
        editor.icursor("end")
        self._inline_editor = editor
        self._inline_edit_row_id = row_id
        self._inline_edit_collection_id = cid
        editor.bind("<Return>", lambda e: self._commit_inline_edit())
        editor.bind("<KP_Enter>", lambda e: self._commit_inline_edit())
        editor.bind("<Escape>", lambda e: self._cancel_inline_edit())
        editor.bind("<FocusOut>", lambda e: self._commit_inline_edit())

    def _commit_inline_edit(self):
        if not self._inline_editor or not self._inline_edit_row_id:
            return
        row_id = self._inline_edit_row_id
        # 편집을 시작한 컬렉션. 편집 중에 다른 컬렉션을 클릭하면 컬렉션 선택이 먼저 바뀐 뒤
        # (<<ListboxSelect>> -> _refresh_items) 그 안에서 편집이 확정되므로, 확정 시점의 선택
        # 컬렉션으로 항목을 찾으면 엉뚱한 컬렉션을 뒤져 편집이 버려짐. 그래서 시작한 컬렉션 id로 찾음
        edit_cid = self._inline_edit_collection_id
        new_value = self._inline_editor.get().strip()
        editor = self._inline_editor
        # 편집창(Entry)이 사라지기 전, 아직 그 안에 포커스가 있었는지 기억해둠. Enter로
        # 편집을 마친 경우엔 그렇지만, 다른 위젯(예: 컬렉션 목록)을 클릭해서 FocusOut으로
        # 편집이 끝난 경우엔 이미 포커스가 그쪽으로 옮겨간 뒤이므로 해당하지 않음
        editor_had_focus = (self.app.root.focus_get() is editor)
        self._inline_editor = None
        self._inline_edit_row_id = None
        self._inline_edit_collection_id = None
        try:
            editor.destroy()
        except tk.TclError:
            pass
        if editor_had_focus:
            # 편집창이 사라진 뒤 포커스가 어디로도 가지 않으면 방향키로 항목 목록을 탐색할 수
            # 없으므로 항목 목록으로 되돌림 (다른 위젯을 클릭해 편집을 끝낸 경우는 그 포커스
            # 이동을 존중해 건드리지 않음)
            self.items_tree.focus_set()
        if not new_value:
            self.app.show_status_message("제목은 비워둘 수 없어 변경하지 않았습니다.")
            return
        cid = edit_cid or self._get_selected_collection_id()
        if cid and self._find_item(cid, row_id):
            self._update_item_data(cid, row_id, title=new_value)
            # 지금 보고 있는 컬렉션이 편집한 컬렉션일 때만 목록을 다시 그림. 다른 컬렉션으로
            # 옮겨가는 중이면(호출한 쪽인 _refresh_items가 곧 새 컬렉션의 항목으로 다시 그림)
            # 건드리지 않음
            if cid == self._get_selected_collection_id():
                self._refresh_items(select_item_id=row_id)
            self.app.show_status_message("항목을 수정했습니다.")

    def _cancel_inline_edit(self):
        if self._inline_editor:
            editor = self._inline_editor
            self._inline_editor = None
            self._inline_edit_row_id = None
            self._inline_edit_collection_id = None
            try:
                editor.destroy()
            except tk.TclError:
                pass
            # 편집을 취소(Esc)했을 때도 같은 이유로 포커스를 항목 목록에 되돌려줌
            self.items_tree.focus_set()

    # ---- 가져오기/내보내기/백업 훅 (일반메모 탭의 같은 절 설명 참고) ----

    transfer_label = "컬렉션"
    transfer_filename = "collections.json"

    def transfer_parse(self, raw):
        """collections.json과 같은 {"collections": [...]} 형태인지 검증하고 정규화함
        (잘못되면 TypeError/ValueError). "엣지 컬렉션 매니저"가 만든 파일도 읽을 수 있음."""
        if not isinstance(raw, dict) or not isinstance(raw.get("collections"), list):
            raise TypeError('데이터가 {"collections": [...]} 형태가 아닙니다.')
        # 항목/폴더 id가 겹치면 새로 만듦 (직접 편집한 파일 대비)
        seen_parents, seen_items = set(), set()
        cleaned = []
        for col in raw["collections"]:
            if not isinstance(col, dict):
                raise ValueError("컬렉션 항목이 딕셔너리가 아닙니다.")
            raw_items = col.get("items", [])
            if not isinstance(raw_items, list):
                raise ValueError("컬렉션의 항목 목록이 리스트가 아닙니다.")
            items = []
            for it in raw_items:
                if not isinstance(it, dict):
                    raise ValueError("항목이 딕셔너리가 아닙니다.")
                items.append({
                    "id": unique_id(it.get("id"), seen_items),
                    "title": str(it.get("title", "")),
                    "url": str(it.get("url", "")),
                    "memo": str(it.get("memo", "")),
                    "added": str(it.get("added", "")),
                })
            cleaned.append({
                "id": unique_id(col.get("id"), seen_parents),
                "name": str(col.get("name", "이름 없음")),
                "created": str(col.get("created", "")),
                "items": items,
            })
        return {"collections": cleaned}

    def transfer_summary(self, data):
        cols = data["collections"]
        return f"컬렉션 {len(cols)}개 (항목 {sum(len(c['items']) for c in cols)}개)"

    def transfer_apply(self, data):
        # 편집 중이던 인라인 편집은 곧 사라질 이전 데이터에 대한 것이므로 커밋하지 않고 버림
        self._cancel_inline_edit()
        self.data = data
        ok = self.app.save_collections()
        self._refresh_collections()
        return ok

    def transfer_export_json(self):
        return self.data

    def transfer_export_txt(self):
        out = []
        for col in self.data["collections"]:
            out.append(f"[{col['name']}]\n")
            for it in col["items"]:
                out.append(f"- {it.get('title', '')}\n")
                if it.get("url"):
                    out.append(f"  URL: {it['url']}\n")
                if it.get("memo"):
                    out.append(f"  메모: {it['memo']}\n")
            out.append("\n")
        return "".join(out)

    def transfer_export_xlsx(self):
        rows = [[col["name"], it.get("title", ""), it.get("url", ""), it.get("memo", "")]
                for col in self.data["collections"] for it in col["items"]]
        return "컬렉션", ["컬렉션", "제목", "URL", "메모"], rows


class MemoApp:
    """최상위 지휘자: 메뉴, 전역 단축키, 창 생명주기, 테마/상태표시줄처럼 여러
    탭을 넘나드는 것만 여기 남기고, 각 탭 자체의 UI/데이터/동작은
    GeneralMemoTab / CalendarMemoTab / ChecklistTab / CollectionTab에 위임함."""

    def __init__(self, root):
        self.root = root
        self.root.title("알파카 다이어리 (Alpaca Diary)")
        self.root.minsize(800, 600)
        # 아이콘 설정 (오류 발생 시 무시)
        # default=를 지정하면 타이틀바뿐 아니라 작업표시줄 아이콘, 그리고 이후에
        # 열리는 설정/일괄삭제 같은 팝업 창에도 같은 아이콘이 적용됨
        try:
            self.root.iconbitmap(default=resource_path("ad.ico"))
        except Exception as e:
            print(f"아이콘 로드 실패: {e}")

        self.store = MemoStore(get_app_dir())
        self.settings_mgr = SettingsManager(self)

        # 디바운스된 자동저장 예약을 key별로 추적 ({key: after_id})
        self._pending_save_ids = {}
        # 자동저장이 실패한 key를 기록 - 같은 원인(디스크 꽉 참, 권한 없음 등)이
        # 계속되는 동안 키 입력마다 반복해서 오류 팝업이 뜨지 않도록, 이미 알린
        # key는 그 저장이 다시 성공하기 전까지는 조용히 넘어감
        self._save_failed_keys = set()
        # 상태표시줄 임시 메시지(예: 컬렉션 탭의 "제목을 가져오는 중...")의 일련번호. 먼저 예약된
        # 메시지의 "원래대로 복귀" 타이머가 나중 메시지를 덮어쓰지 않도록, 자신이 아직 최신인지
        # 이 번호로 확인함
        self._status_msg_token = 0

        # Windows 11 스타일(sv_ttk) 테마 적용 (sv_ttk 미설치 시 기본 ttk 테마 사용)
        if sv_ttk:
            sv_ttk.set_theme(self.settings_mgr.theme_mode, self.root)
        apply_titlebar_theme(self.root, self.settings_mgr.theme_mode == "dark")
        # sv_ttk는 테마 변경 시 <<ThemeChanged>> 이벤트(큐에 쌓임)로 위젯 색상을 갱신하는데,
        # 이 처리가 끝나기 전에 위젯을 만들면 일부가 기본 회색(#d9d9d9 계열)으로 만들어지므로
        # 위젯 생성 전에 큐를 한 번 비움
        self.root.update_idletasks()

        # 상태표시줄 생성 (side=BOTTOM으로 먼저 pack해야, 이후 fill=BOTH+expand=True로
        # pack되는 notebook이 이 영역까지 침범하지 않음 - pack은 호출 순서대로 공간을 배정함)
        self.status_bar = ttk.Label(root, text="", relief=tk.SUNKEN, anchor=tk.W, font=("맑은 고딕", 10))
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)

        # 메뉴막대 아래 최상위 탭 - 하위의 [월별보기]/[1년전체보기]/[목록보기] 탭과 구분되도록
        # 최상위 탭 전용 스타일(더 큰 볼드체 + 넉넉한 여백)을 적용함.
        top_tab_style = ttk.Style()
        top_tab_style.configure("TopLevel.TNotebook.Tab", font=("맑은 고딕", 13, "bold"),
                                padding=(24, 4))
        top_tab_style.configure("TopLevel.TNotebook", tabmargins=(6, 8, 6, 0))

        self.notebook = ttk.Notebook(root, style="TopLevel.TNotebook")
        self.notebook.pack(fill=tk.BOTH, expand=True)

        general_frame = ttk.Frame(self.notebook)
        calendar_frame = ttk.Frame(self.notebook)
        checklist_frame = ttk.Frame(self.notebook)
        collection_frame = ttk.Frame(self.notebook)
        self.notebook.add(general_frame, text="📝 일반메모")
        self.notebook.add(calendar_frame, text="📅 달력메모")
        self.notebook.add(checklist_frame, text="✅ 체크리스트")
        self.notebook.add(collection_frame, text="📚 컬렉션")

        self.general_tab = GeneralMemoTab(general_frame, self)
        self.calendar_tab = CalendarMemoTab(calendar_frame, self)
        self.checklist_tab = ChecklistTab(checklist_frame, self)
        self.collection_tab = CollectionTab(collection_frame, self)
        # 새 탭을 추가하려면 위처럼 만든 뒤 여기 리스트에 추가하면, 테마/글꼴/
        # 상태표시줄이 자동으로 그 탭까지 반영함 (파일 위 안내 주석 참고).
        # 이 리스트 순서는 반드시 위 notebook.add() 순서와 같아야 함 - _active_tab()이
        # notebook 탭 인덱스로 이 리스트를 그대로 찾아 쓰기 때문
        self.tabs = [self.general_tab, self.calendar_tab, self.checklist_tab, self.collection_tab]
        self._last_active_tab = self.tabs[0]

        self.create_menu()

        # ---- 단축키 등록 ----
        # 아래는 전부 root 레벨에 한 번만 바인딩하고, 실제 동작은 그 순간의 활성
        # 탭(self._active_tab())에게 위임한다. 각 라우터 메서드는 활성 탭에 해당
        # 이름의 메서드가 있으면 호출하고 없으면 조용히 넘어가므로, 새 탭이
        # 그 메서드를 구현하지 않으면 자동으로 이 단축키에서 아무 효과가 없다.
        self.root.bind("<Control-Tab>", lambda event: self._cycle_top_tab(1))
        self.root.bind("<Control-Shift-Tab>", lambda event: self._cycle_top_tab(-1))

        # 공통 단축키 (탭마다 의미가 다름 - 각 라우터 메서드 주석 참고)
        self.root.bind("<Control-n>", self._on_ctrl_n_key)
        self.root.bind("<Control-d>", self._on_ctrl_d_key)
        self.root.bind("<Control-m>", self._on_ctrl_m_key)
        self.root.bind("<Control-l>", self.focus_on_listbox)
        self.root.bind("<Control-t>", self.focus_on_title)
        self.root.bind("<Prior>", self._on_prior_key)
        self.root.bind("<Next>", self._on_next_key)
        self.root.bind("<Alt-t>", self.insert_datetime)
        # 빠른 입력 단축키 (Alt+1 ~ Alt+9, Alt+0)
        # Windows에서는 <Alt-1>처럼 특정 숫자 keysym을 그대로 bind()하면
        # WM_SYSKEYDOWN 처리 특성상 이벤트가 씹혀 동작하지 않는 경우가 있어,
        # <Alt-KeyPress>로 Alt+모든 키 입력을 받은 뒤 내부에서 눌린 키를 판별한다.
        self.root.bind("<Alt-KeyPress>", self._on_alt_number_keypress)

        # 탭 전용 단축키 (구현한 탭이 활성화되어 있을 때만 동작함)
        self.root.bind("<Alt-m>", self._on_alt_m_key)
        self.root.bind("<Alt-y>", self._on_alt_y_key)
        self.root.bind("<Alt-l>", self._on_alt_l_key)
        self.root.bind("<Alt-h>", self._on_alt_h_key)
        self.root.bind("<Alt-Left>", self._on_alt_left_key)
        self.root.bind("<Alt-Right>", self._on_alt_right_key)
        # 고급 사용자용 숨김 기능: 버튼 없이 단축키로만 진입 (달력메모 탭 전용)
        self.root.bind("<Control-Shift-D>", self._on_ctrl_shift_d_key)
        self.root.bind("<Control-Shift-N>", self._on_ctrl_shift_n_key)
        self.root.bind("<F2>", self._on_f2_key)
        self.root.bind("<F1>", self._show_shortcut_help)

        # 복사 단축키는 설정에 따라 바인딩
        self.settings_mgr.bind_copy_shortcut()
        self.notebook.bind("<<NotebookTabChanged>>", self.on_tab_changed)

        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
        self.general_tab.toggle_right_panel(False)
        self.apply_theme_colors()
        self.update_status_bar()

        # UI 생성 완료 후 창 위치/크기 복원
        self.restore_window_geometry()

        # 시작 시 테마 미적용 보정: 위젯이 아직 없거나 창이 화면에 표시되기 전에 테마를 적용하면
        # 메뉴/버튼/라벨/타이틀바 일부가 테마를 제대로 못 받는 경우가 있어, 창이 완전히 그려진
        # 뒤 테마를 한 번 더 적용함
        self.root.after(150, self._reapply_theme_on_startup)
        self.root.after(400, self._notify_holiday_problems)
        self.root.after(700, self._notify_load_problems)

    # ---- 저장/자동저장 (MemoStore를 감싸는 얇은 래퍼: 실패 시 알림 대상 key 관리) ----

    def _after_save(self, key, ok, notify):
        """저장 결과 처리: 성공하면 '알린 실패' 기록을 지우고, 실패하면(notify일 때) 팝업으로 알림.
        notify=False는 종료 처리처럼 호출한 쪽이 직접 안내하는 경우에 씀."""
        if ok:
            self._save_failed_keys.discard(key)
        elif notify:
            self._notify_save_failure(key)

    def save_memos(self, notify=True):
        ok = self.store.save_memos(self.general_tab.memos)
        self._after_save("memos", ok, notify)
        return ok

    def save_calendar_memos(self, notify=True):
        ok = self.store.save_calendar_memos(self.calendar_tab.calendar_memos)
        self._after_save("calendar_memos", ok, notify)
        return ok

    def save_collections(self, notify=True):
        ok = self.store.save_collections(self.collection_tab.data)
        self._after_save("collections", ok, notify)
        return ok

    def save_checklists(self, notify=True):
        ok = self.store.save_checklists(self.checklist_tab.data)
        self._after_save("checklists", ok, notify)
        return ok

    def _debounced_save(self, key, save_func, delay_ms=AUTOSAVE_DEBOUNCE_MS):
        """key로 구분되는 저장을 delay_ms 뒤로 미루고, 그 사이에 또 호출되면
        이전 예약을 취소하고 다시 미룸. (연속으로 키 입력이 들어오는 동안은
        디스크에 쓰지 않다가, 입력이 멈추고 delay_ms가 지나야 실제로 한 번
        저장 - 매 키 입력마다 파일 전체를 쓰는 부담을 줄임)"""
        existing = self._pending_save_ids.pop(key, None)
        if existing is not None:
            self.root.after_cancel(existing)

        def _run():
            self._pending_save_ids.pop(key, None)
            result = save_func()
            # save_func가 명시적으로 False를 반환한 경우만 저장 실패로 간주함
            # (달력 그리드 다시 그리기처럼 반환값이 없는 콜백은 영향받지 않음)
            if result is False:
                self._notify_save_failure(key)

        self._pending_save_ids[key] = self.root.after(delay_ms, _run)

    def _notify_save_failure(self, key):
        """자동저장 실패를 사용자에게 알림. 콘솔 출력만으로는 콘솔 없이 실행되는
        빌드(exe)에서 사용자가 저장 실패 사실을 전혀 알 수 없으므로 팝업으로 알림.
        단, 같은 원인(디스크 꽉 참 등)으로 계속 실패하는 동안 키 입력마다 팝업이
        반복해서 뜨지 않도록, 이미 알린 key는 그 저장이 다시 성공할 때까지 무시함."""
        if key in self._save_failed_keys:
            return
        self._save_failed_keys.add(key)
        label = {"memos": "일반메모", "calendar_memos": "달력메모", "collections": "컬렉션",
                  "checklists": "체크리스트"}.get(key, key)
        error = self.store.last_write_error
        if isinstance(error, WriteBlockedError):
            # 시작할 때 읽지 못한 파일: 디스크/권한 문제가 아니라 덮어쓰기 방지 때문이므로 그 사유만 안내
            detail = f"{error}\n"
        elif error is not None:
            detail = f"사유: {error}\n디스크 공간이나 저장 폴더의 쓰기 권한을 확인해주세요.\n"
        else:
            detail = "디스크 공간이나 저장 폴더의 쓰기 권한을 확인해주세요.\n"
        messagebox.showerror(
            "저장 실패",
            f"{label} 저장에 실패했습니다.\n{detail}"
            "입력한 내용은 화면에 남아있지만 파일에는 아직 저장되지 않았습니다.",
            parent=self.root,
        )

    def _cancel_pending_saves(self):
        """예약된 디바운스 저장을 전부 취소만 함 (뒤이어 직접·즉시 저장을
        호출할 예정일 때 사용 - 예: 종료 직전)"""
        for after_id in self._pending_save_ids.values():
            self.root.after_cancel(after_id)
        self._pending_save_ids.clear()

    # ---- 탭 전반에 걸친 것들: 메뉴/테마/상태표시줄/복사/삽입 ----

    def create_menu(self):
        menubar = tk.Menu(self.root)
        self.file_menu = tk.Menu(menubar, tearoff=0, postcommand=self._update_file_menu)
        # 가져오기/내보내기는 "지금 보고 있는 탭"의 데이터에 대해 동작하고, 라벨에 그 탭 이름이
        # 표시됨 (_update_file_menu 참고)
        self.file_menu.add_command(label="가져오기...", command=self.import_current_tab)
        self.file_menu.add_command(label="내보내기...", command=self.export_current_tab)
        self.file_menu.add_separator()
        self.file_menu.add_command(label="전체 백업 (zip)...", command=self.backup_all)
        self.file_menu.add_command(label="백업에서 복원...", command=self.restore_all)
        self.file_menu.add_separator()
        self.file_menu.add_command(label="종료", command=self.on_closing)
        menubar.add_cascade(label="파일", menu=self.file_menu)

        settings_menu = tk.Menu(menubar, tearoff=0)
        settings_menu.add_command(label="글꼴 설정...", command=self.settings_mgr.open_font_settings)
        settings_menu.add_command(label="단축키 설정...", command=self.settings_mgr.open_shortcut_settings)
        settings_menu.add_command(label="빠른 입력 설정...", command=self.settings_mgr.open_quick_input_settings)
        settings_menu.add_command(label="테마 설정...", command=self.settings_mgr.open_theme_settings)
        menubar.add_cascade(label="설정", menu=settings_menu)

        help_menu = tk.Menu(menubar, tearoff=0)
        help_menu.add_command(label="단축키 안내", command=self._show_shortcut_help, accelerator="F1")
        help_menu.add_separator()
        help_menu.add_command(label="프로그램 정보", command=lambda: self._open_help_link(PROGRAM_INFO_URL))
        help_menu.add_command(label="알파카 툴즈로 이동", command=lambda: self._open_help_link(ALPACA_TOOLS_URL))
        help_menu.add_command(label="제작자 블로그로 이동", command=lambda: self._open_help_link(AUTHOR_BLOG_URL))
        menubar.add_cascade(label="도움말", menu=help_menu)

        self.root.config(menu=menubar)
        self._update_file_menu()

    # ---- 파일 메뉴: 가져오기/내보내기(현재 탭 기준) + 전체 백업/복원 ----
    # 가져오기/내보내기는 활성 탭의 데이터만 다루므로 메뉴 항목은 탭 수와 상관없이 하나씩임.
    # 각 탭은 transfer_* 훅(파일 위 "앱 구조 안내" 참고)만 제공하고, 파일 선택/확인창/
    # 형식별(JSON·TXT·XLSX) 저장 흐름은 여기서 공통 처리함. 여러 탭의 데이터를 한 번에
    # 옮길 때는 전체 백업(zip)/백업에서 복원을 씀.

    _FILE_MENU_IMPORT = 0
    _FILE_MENU_EXPORT = 1

    def _update_file_menu(self):
        """파일 메뉴가 열리기 직전에 호출되어, 가져오기/내보내기 라벨에 활성 탭 이름을 표시함.
        (가져오기/내보내기 훅을 구현하지 않은 탭이면 두 항목을 비활성화함)"""
        label = getattr(self._active_tab(), "transfer_label", None)
        if label:
            import_text, export_text, state = f"[{label}] 가져오기...", f"[{label}] 내보내기...", tk.NORMAL
        else:
            import_text, export_text, state = "가져오기...", "내보내기...", tk.DISABLED
        self.file_menu.entryconfigure(self._FILE_MENU_IMPORT, label=import_text, state=state)
        self.file_menu.entryconfigure(self._FILE_MENU_EXPORT, label=export_text, state=state)

    def _transfer_tabs(self):
        """가져오기/내보내기/백업에 참여하는(transfer_filename을 가진) 탭들"""
        return [tab for tab in self.tabs if getattr(tab, "transfer_filename", None)]

    @staticmethod
    def _parse_transfer_text(tab, text):
        """JSON 텍스트를 읽어 그 탭의 transfer_parse로 검증/정규화한 데이터를 반환"""
        if not text.strip():
            raise EmptyTransferFileError()
        return tab.transfer_parse(json.loads(text))

    @staticmethod
    def _describe_transfer_error(label, error):
        if isinstance(error, EmptyTransferFileError):
            return "파일이 비어있습니다."
        if isinstance(error, json.JSONDecodeError):
            return "올바른 JSON 파일이 아닙니다."
        if isinstance(error, UnicodeDecodeError):
            return "UTF-8 텍스트(JSON) 파일이 아닙니다."
        if isinstance(error, (TypeError, ValueError)):
            return f"{label} 파일 구조가 올바르지 않습니다: {error}"
        return f"파일을 가져오는 중 오류 발생: {error}"

    def import_current_tab(self):
        """파일 > [현재 탭] 가져오기...: JSON 파일의 내용으로 활성 탭의 데이터를 덮어씀"""
        tab = self._active_tab()
        label = getattr(tab, "transfer_label", None)
        if not label:
            return
        filepath = filedialog.askopenfilename(
            title=f"[{label}] 가져오기 (JSON 파일만 지원)",
            filetypes=[("JSON 파일", "*.json"), ("모든 파일", "*.*")],
            parent=self.root,
        )
        if not filepath:
            return
        try:
            # utf-8-sig: 메모장 등으로 저장해 BOM이 붙은 JSON 파일도 읽을 수 있게 함
            with open(filepath, "r", encoding="utf-8-sig") as f:
                text = f.read()
            data = self._parse_transfer_text(tab, text)
            if not messagebox.askyesno(
                    "확인",
                    f"기존 [{label}] 데이터를 모두 덮어쓰고 가져오시겠습니까?\n\n"
                    f"(실행 직전에 현재 데이터가 {AUTO_BACKUP_DIRNAME} 폴더에 자동 백업됩니다.)",
                    parent=self.root):
                return
            proceed, backup_path = self.auto_backup_before("before-import")
            if not proceed:
                return
            ok = tab.transfer_apply(data)
            self.update_status_bar()
            if ok:
                messagebox.showinfo(
                    "성공", f"[{label}] 데이터를 성공적으로 가져왔습니다." + self.backup_note(backup_path),
                    parent=self.root)
            else:
                messagebox.showwarning(
                    "저장 실패",
                    f"[{label}] 데이터를 화면에는 반영했지만 파일 저장에 실패했습니다.\n"
                    "디스크 공간이나 저장 폴더의 쓰기 권한을 확인해주세요." + self.backup_note(backup_path),
                    parent=self.root)
        except Exception as e:
            messagebox.showerror("오류", self._describe_transfer_error(label, e), parent=self.root)

    def export_current_tab(self):
        """파일 > [현재 탭] 내보내기...: 활성 탭의 데이터를 JSON/TXT/XLSX로 저장.
        JSON만 다시 가져올 수 있고, TXT/XLSX는 보관·열람용임 (저장 형식 목록과 완료 안내에 표시)"""
        tab = self._active_tab()
        label = getattr(tab, "transfer_label", None)
        if not label:
            return
        filepath = filedialog.asksaveasfilename(
            title=f"[{label}] 내보내기", defaultextension=".json",
            filetypes=[("JSON 파일 (다시 가져오기 가능)", "*.json"),
                       ("텍스트 파일 (보관·열람용)", "*.txt"),
                       ("Excel 파일 (보관·열람용)", "*.xlsx")],
            parent=self.root,
        )
        if not filepath:
            return
        file_ext = os.path.splitext(filepath)[1].lower()
        truncated_cells = 0
        try:
            if file_ext == ".json":
                self.store.write_json(filepath, tab.transfer_export_json())
            elif file_ext == ".txt":
                with open(filepath, "w", encoding="utf-8") as f:
                    f.write(tab.transfer_export_txt())
            elif file_ext == ".xlsx":
                if not openpyxl:
                    messagebox.showerror("오류", "Excel 내보내기에는 openpyxl이 필요합니다.", parent=self.root)
                    return
                sheet_title, header, rows = tab.transfer_export_xlsx()
                wb = openpyxl.Workbook()
                ws = wb.active
                ws.title = sheet_title
                append_xlsx_row(ws, header)
                for row in rows:
                    truncated_cells += append_xlsx_row(ws, row)
                wb.save(filepath)
            else:
                # .json/.txt/.xlsx가 아닌 확장자(저장 대화상자에서 직접 입력한 경우)면 아무 것도
                # 저장하지 않았는데 아래 "성공" 메시지가 뜨지 않도록 명시적으로 오류 처리함
                raise ValueError(
                    f"지원하지 않는 파일 형식입니다: {file_ext or '(확장자 없음)'}\n"
                    ".json / .txt / .xlsx 중 하나로 저장해주세요."
                )
            message = f"[{label}] 데이터를 {filepath} 파일로 내보냈습니다."
            if file_ext != ".json":
                message += "\n\nTXT/Excel 파일은 보관·열람용이며, 가져오기는 JSON 파일만 지원합니다."
            if truncated_cells:
                message += (f"\n\nExcel 한 셀의 최대 글자 수({XLSX_MAX_CELL_CHARS:,}자)를 넘는 "
                            f"{truncated_cells}개 셀은 잘려서 저장되었습니다. 전체 내용은 JSON으로 내보내세요.")
            messagebox.showinfo("성공", message, parent=self.root)
        except Exception as e:
            messagebox.showerror("오류", f"파일 내보내기 중 오류 발생: {e}", parent=self.root)

    def _commit_inline_edits(self):
        """열려 있는 인라인 편집(컬렉션/체크리스트)을 확정해 데이터에 반영함 (백업/종료 직전에 사용)"""
        for tab in self.tabs:
            commit = getattr(tab, "on_deactivated", None)
            if commit:
                commit()

    def auto_backup_before(self, reason, parent=None):
        """되돌릴 수 없는 작업(가져오기/복원/달력메모 일괄삭제)을 하기 직전에 현재 전체 데이터를
        backup_auto 폴더에 ZIP으로 자동 백업함. 백업은 파일이 아니라 지금 메모리에 있는 최신
        데이터를 담음(backup_all과 같은 방식). 이 ZIP은 '백업에서 복원...'으로 그대로 되돌릴 수 있음.

        반환: (계속 진행할지, 만든 백업 파일 경로 또는 None). 백업에 실패하면 사용자에게
        백업 없이 계속할지 물어서 그 답을 반환함."""
        parent = parent or self.root
        try:
            self._commit_inline_edits()
            files = {}
            for tab in self._transfer_tabs():
                files[tab.transfer_filename] = json.dumps(
                    tab.transfer_export_json(), ensure_ascii=False, indent=4)
            return True, self.store.write_auto_backup(files, reason)
        except Exception as e:
            proceed = messagebox.askyesno(
                "자동 백업 실패",
                f"작업 전에 현재 데이터를 자동 백업하지 못했습니다.\n({e})\n\n"
                "백업 없이 계속 진행하시겠습니까?",
                icon="warning", parent=parent)
            return proceed, None

    @staticmethod
    def backup_note(backup_path):
        """자동 백업을 만들었을 때 완료 안내에 덧붙일 문구 (백업이 없으면 빈 문자열)"""
        if not backup_path:
            return ""
        shown = os.path.join(AUTO_BACKUP_DIRNAME, os.path.basename(backup_path))
        return (f"\n\n작업 전 데이터를 자동 백업해 두었습니다:\n{shown}\n"
                "(되돌리려면 파일 > 백업에서 복원... 에서 이 파일을 선택하세요)")

    def backup_all(self):
        """파일 > 전체 백업 (zip)...: 모든 탭의 데이터 파일을 ZIP 하나로 묶어 저장.
        디스크의 파일이 아니라 지금 메모리에 있는 최신 데이터를 담으므로, 자동저장이
        아직 반영되지 않은 마지막 입력도 포함됨."""
        # 열려 있는 인라인 편집(컬렉션/체크리스트)을 먼저 확정해 백업에 포함시킴 (종료 시 저장과 같은 방식)
        self._commit_inline_edits()
        filepath = filedialog.asksaveasfilename(
            title="전체 백업", defaultextension=".zip",
            initialfile=f"AlpacaDiary_backup_{datetime.now():%Y%m%d_%H%M}.zip",
            filetypes=[("ZIP 파일", "*.zip")],
            parent=self.root,
        )
        if not filepath:
            return
        try:
            files = {}
            summaries = []
            for tab in self._transfer_tabs():
                data = tab.transfer_export_json()
                files[tab.transfer_filename] = json.dumps(data, ensure_ascii=False, indent=4)
                summaries.append(f"· {tab.transfer_label}: {tab.transfer_summary(data)}")
            self.store.write_backup_zip(filepath, files)
            messagebox.showinfo(
                "성공", f"전체 백업을 만들었습니다.\n{filepath}\n\n" + "\n".join(summaries), parent=self.root)
        except Exception as e:
            messagebox.showerror("오류", f"백업 중 오류 발생: {e}", parent=self.root)

    def restore_all(self):
        """파일 > 백업에서 복원...: 전체 백업 ZIP(또는 같은 이름의 데이터 파일이 들어 있는 ZIP)의
        내용으로 탭별 데이터를 덮어씀. 먼저 ZIP 안의 모든 파일을 검증하고, 하나라도 문제가
        있으면 아무것도 바꾸지 않음 (일부 탭만 복원되는 어중간한 상태를 막기 위함)."""
        filepath = filedialog.askopenfilename(
            title="백업에서 복원",
            filetypes=[("ZIP 파일", "*.zip"), ("모든 파일", "*.*")],
            parent=self.root,
        )
        if not filepath:
            return
        tabs = self._transfer_tabs()
        try:
            texts = self.store.read_backup_zip(filepath, {tab.transfer_filename for tab in tabs})
            if not texts:
                messagebox.showerror(
                    "오류",
                    "백업 파일 안에서 알파카 다이어리 데이터 파일을 찾을 수 없습니다.\n"
                    f"({', '.join(tab.transfer_filename for tab in tabs)})",
                    parent=self.root)
                return
            parsed = []
            for tab in tabs:
                text = texts.get(tab.transfer_filename)
                if text is None:
                    continue
                try:
                    parsed.append((tab, self._parse_transfer_text(tab, text)))
                except Exception as e:
                    messagebox.showerror(
                        "오류",
                        f"백업 파일 안의 {tab.transfer_filename}을 읽을 수 없습니다.\n"
                        f"{self._describe_transfer_error(tab.transfer_label, e)}\n\n"
                        "복원은 진행되지 않았고 현재 데이터는 그대로입니다.",
                        parent=self.root)
                    return

            message = "백업 파일의 내용으로 다음 데이터를 모두 덮어씁니다:\n\n" + "\n".join(
                f"· {tab.transfer_label}: {tab.transfer_summary(data)}" for tab, data in parsed)
            kept = [tab.transfer_label for tab in tabs if tab.transfer_filename not in texts]
            if kept:
                message += "\n\n백업에 없어 그대로 유지되는 데이터: " + ", ".join(kept)
            message += (f"\n\n실행 직전에 현재 데이터가 {AUTO_BACKUP_DIRNAME} 폴더에 자동 백업되며, "
                        "필요하면 같은 메뉴에서 되돌릴 수 있습니다. 계속하시겠습니까?")
            if not messagebox.askyesno("백업에서 복원", message, icon="warning", parent=self.root):
                return
            proceed, backup_path = self.auto_backup_before("before-restore")
            if not proceed:
                return

            problems = []
            for tab, data in parsed:
                try:
                    if not tab.transfer_apply(data):
                        problems.append(tab.transfer_label)
                except Exception as e:
                    problems.append(f"{tab.transfer_label} ({e})")
            self.update_status_bar()
            if problems:
                messagebox.showwarning(
                    "복원 중 문제 발생",
                    "다음 데이터는 복원 중 저장에 문제가 있었습니다:\n· " + "\n· ".join(problems) + "\n\n"
                    "디스크 공간이나 저장 폴더의 쓰기 권한을 확인해주세요.",
                    parent=self.root)
            else:
                messagebox.showinfo("성공", "백업에서 복원했습니다." + self.backup_note(backup_path),
                                    parent=self.root)
        except zipfile.BadZipFile:
            messagebox.showerror("오류", "올바른 ZIP 백업 파일이 아닙니다.", parent=self.root)
        except Exception as e:
            messagebox.showerror("오류", f"복원 중 오류 발생: {e}", parent=self.root)

    def _active_tab(self):
        idx = self.notebook.index(self.notebook.select())
        return self.tabs[idx]

    def _dispatch_to_active_tab(self, method_name, event=None):
        """활성 탭에 method_name 메서드가 있으면 event를 넘겨 호출하고 그 결과를
        반환하며, 없으면 아무 일도 하지 않고 None을 반환함. 공통/탭 전용 단축키
        라우터들이 공유하는 핵심 로직 (파일 위 "앱 구조 안내" 참고)."""
        method = getattr(self._active_tab(), method_name, None)
        if method:
            return method(event)
        return None

    def apply_theme_colors(self):
        """ttk가 테마를 입히지 못하는 Listbox/Text/달력 Canvas/컬렉션 인라인편집
        위젯에 현재 테마 색상을 적용. (Frame/Label/Entry/Button/Treeview 등은
        sv_ttk가 자동으로 처리함) 각 탭의 위젯 색칠은 그 탭 스스로 담당하고
        (apply_theme_colors), 여기서는 모든 탭에 방송만 함 - 새 탭을 추가해도
        이 메서드는 그대로 둬도 됨."""
        colors = THEME_COLORS.get(self.settings_mgr.theme_mode, THEME_COLORS["light"])
        for tab in self.tabs:
            tab.apply_theme_colors(colors)

    def update_status_bar(self, event=None):
        try:
            self.status_bar.config(text=self._active_tab().get_status_text())
        except Exception:
            pass

    def show_status_message(self, message, duration_ms=4000):
        """탭 내부 동작(예: 컬렉션 탭의 항목 추가/삭제/제목 가져오기 결과)을 상태표시줄에
        잠시 보여주고, duration_ms 후 원래 상태 문구(get_status_text())로 되돌림.
        (일반메모/달력메모의 "복사 완료!" 표시는 각 탭 전용 라벨을 쓰므로 이 메서드와
        무관함 - 이건 공유 상태표시줄에 표시하고 싶은 탭이면 어디서든 재사용 가능함)"""
        self._status_msg_token += 1
        token = self._status_msg_token
        self.status_bar.config(text=message)
        self.root.after(duration_ms, lambda: self._clear_status_message(token))

    def _clear_status_message(self, token):
        if token == self._status_msg_token:
            self.update_status_bar()

    def copy_to_clipboard(self, event=None):
        """활성 탭에 맞는 내용을 복사 (각 탭의 get_copy_target()이 대상을 알려줌.
        일반메모/달력메모는 내용 편집창의 글을, 체크리스트/컬렉션은 선택한 항목을 정해진
        양식의 문장으로 만들어 복사함. 복사할 대상이 없는 상태(항목을 선택하지 않음)는
        None을 반환해 아무 일도 일어나지 않음 - [클립보드로 복사] 버튼이 비활성화된
        상태와 같음)"""
        target = self._active_tab().get_copy_target()
        if target is None:
            return "break"
        return self._copy_text_to_clipboard(*target)

    def _copy_text_to_clipboard(self, source, status_label):
        """source: 내용을 가져올 tk.Text 위젯, 또는 복사할 문자열을 돌려주는 함수"""
        try:
            if isinstance(source, tk.Text):
                text_to_copy = source.get("1.0", tk.END).strip()
            else:
                text_to_copy = (source() or "").strip()
            if not text_to_copy:
                messagebox.showinfo("알림", "복사할 내용이 없습니다.", parent=self.root)
                return "break"
            self.root.clipboard_clear()
            self.root.clipboard_append(text_to_copy)

            # "복사 완료!" 메시지 표시
            self._show_copy_success(status_label)

        except tk.TclError:
            messagebox.showerror("오류", "클립보드에 접근할 수 없습니다.", parent=self.root)
        except Exception as e:
            messagebox.showerror("오류", f"알 수 없는 오류 발생: {e}", parent=self.root)
        return "break"

    def _show_copy_success(self, label):
        """복사 완료 메시지를 1초 동안 표시 (라이트=파란색, 다크=노란색)"""
        colors = THEME_COLORS.get(self.settings_mgr.theme_mode, THEME_COLORS["light"])
        label.config(text="복사 완료!", foreground=colors["success_fg"])
        # 1초(1000ms) 후에 메시지 제거
        self.root.after(1000, lambda: label.config(text=""))

    def _insert_text_at_focus(self, text):
        """포커스된 위젯의 커서 위치에 문자열을 삽입하는 공통 로직.
        (Alt+T 날짜/시간 삽입, Alt+숫자 빠른 입력에서 공용으로 사용)
        각 탭에게 순서대로 "이 위젯이 네 삽입 대상이니?"라고 물어보고(insert_text_at_widget),
        맞다고 답한 첫 번째 탭에서 멈춘다. 아무 탭도 그 위젯을 모르면(예: 포커스가
        버튼이나 리스트에 있는 경우) 조용히 아무 일도 하지 않는다."""
        focused = self.root.focus_get()
        if focused is None:
            return
        for tab in self.tabs:
            method = getattr(tab, "insert_text_at_widget", None)
            if method and method(focused, text):
                return

    def insert_datetime(self, event=None):
        """Alt+T: 포커스된 위젯의 커서 위치에 현재 날짜/시간을 삽입 (yyyy-mm-dd hh:mm:ss)"""
        now_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        self._insert_text_at_focus(now_str)
        return "break"

    def insert_quick_text(self, key, event=None):
        """Alt+1~Alt+0: 설정 메뉴 > 빠른 입력 설정에서 미리 지정한 문구를 삽입"""
        text = self.settings_mgr.quick_inputs.get(key, "")
        if not text:
            # 해당 슬롯에 등록된 문구가 없으면 아무 동작도 하지 않음
            return "break"
        self._insert_text_at_focus(text)
        return "break"

    def _on_alt_number_keypress(self, event):
        """<Alt-KeyPress> 범용 핸들러: Alt+숫자(1~9,0) 입력만 골라내 빠른 입력을 실행.

        Windows에서 <Alt-1>처럼 특정 keysym을 직접 bind()하면 WM_SYSKEYDOWN 처리
        특성상 이벤트가 씹혀 아예 안 잡히는 경우가 있어, Alt+모든 키를 통째로 받은 뒤
        1) Windows 가상 키코드(keycode)로 먼저 판별하고,
        2) 안되면 keysym으로도 판별하는(리눅스/맥 등 대비) 이중 방식을 사용한다.
        해당하지 않는 Alt 조합(Alt+T 등)은 그대로 통과시켜 다른 바인딩이 처리하게 둔다.
        """
        key = ALT_DIGIT_VK_CODES.get(event.keycode)
        if key is None and event.keysym in QUICK_INPUT_KEYS:
            key = event.keysym
        if key is not None:
            return self.insert_quick_text(key, event)
        return None

    def _show_shortcut_help(self, event=None):
        colors = THEME_COLORS.get(self.settings_mgr.theme_mode, THEME_COLORS["light"])
        ShortcutHelpDialog(self.root, colors)
        return "break"

    def _open_help_link(self, url):
        """[도움말] 메뉴의 링크 항목(프로그램 정보/알파카 툴즈/제작자 블로그): 기본 웹 브라우저로
        url을 엶. 브라우저를 열지 못하면 주소를 알려줘서 직접 열 수 있게 함."""
        try:
            opened = webbrowser.open(url)
        except Exception:
            opened = False
        if not opened:
            messagebox.showwarning(
                "링크 열기 실패",
                f"웹 브라우저를 열지 못했습니다.\n아래 주소를 브라우저에 직접 입력해 주세요.\n\n{url}",
                parent=self.root)

    # ---- 탭을 넘나드는 단축키 라우터 ----
    # 아래 라우터들은 전부 같은 형태다: "활성 탭에 이 이름의 메서드가 있으면 호출하고,
    # 없으면 아무 일도 하지 않는다." 그래서 탭이 늘거나 줄어도 이 메서드들은 손댈 필요 없이,
    # 각 탭 클래스에 그 이름의 메서드를 만들거나 지우기만 하면 된다.

    def _cycle_top_tab(self, direction):
        """Ctrl+Tab(+1)/Ctrl+Shift+Tab(-1): 탭 전환.
        (ttk.Notebook 자체의 기본 Ctrl+Tab 처리는 노트북 위젯 본인이 포커스일
        때만 동작해 평소 편집 중엔 적용되지 않으므로, root 레벨에서 직접 처리함)"""
        tabs = self.notebook.tabs()
        current = self.notebook.index(self.notebook.select())
        self.notebook.select(tabs[(current + direction) % len(tabs)])
        return "break"

    def _on_ctrl_m_key(self, event=None):
        """Ctrl+M: 현재 탭의 "내용" 위젯(또는 항목 목록)에 포커스만 이동함
        (일반메모: content_text / 달력메모: date_content_text / 체크리스트·컬렉션: 항목 목록)"""
        self._dispatch_to_active_tab("focus_content", event)
        return "break"

    def _on_ctrl_n_key(self, event=None):
        """Ctrl+N: 탭마다 "새 항목"의 의미가 다름
        (일반메모: 새 메모 / 달력메모: [추가] 팝업 / 체크리스트: 입력창의 내용을 항목으로
        추가 / 컬렉션: 제목·URL·메모를 한 번에 입력하는 새 항목 편집 창)"""
        method = getattr(self._active_tab(), "on_ctrl_n", None)
        if method:
            return method(event)
        return "break"

    def _on_ctrl_d_key(self, event=None):
        """Ctrl+D: 탭마다 "선택된 것 삭제"의 의미가 다름
        (일반메모: 제목/내용에 포커스가 있을 때 메모 삭제 / 달력메모: 선택된 날짜의 메모 내용
        삭제 / 체크리스트·컬렉션: 선택된 항목 삭제). 목록 자체에 포커스가 있을 때는 이미
        Delete 키가 그 역할을 하고 있으므로 관여하지 않음"""
        return self._dispatch_to_active_tab("on_ctrl_d", event)

    def _on_prior_key(self, event=None):
        """전역 PageUp: 탭마다 의미가 다름 (달력메모는 항상 이전 메모 날짜로 이동,
        일반메모는 목록에 포커스가 있을 때만 순서 이동, 체크리스트/컬렉션은 목록 자체의
        바인딩이 처리하므로 여기서는 아무 일도 하지 않음)"""
        return self._dispatch_to_active_tab("on_page_up", event)

    def _on_next_key(self, event=None):
        """전역 PageDown: _on_prior_key 참고 (반대 방향)"""
        return self._dispatch_to_active_tab("on_page_down", event)

    def focus_on_listbox(self, event=None):
        """Ctrl+L: 탭마다 다른 "목록"에 포커스 (달력메모는 대응하는 목록이 없어
        아무 일도 하지 않음)"""
        self._dispatch_to_active_tab("focus_list", event)
        return "break"

    def focus_on_title(self, event=None):
        """Ctrl+T: 탭마다 다른 "주요 입력창/버튼"으로 이동"""
        self._dispatch_to_active_tab("focus_primary", event)
        return "break"

    def _on_alt_m_key(self, event=None):
        return self._dispatch_to_active_tab("on_alt_m", event)

    def _on_alt_y_key(self, event=None):
        return self._dispatch_to_active_tab("on_alt_y", event)

    def _on_alt_l_key(self, event=None):
        return self._dispatch_to_active_tab("on_alt_l", event)

    def _on_alt_h_key(self, event=None):
        return self._dispatch_to_active_tab("on_alt_h", event)

    def _on_alt_left_key(self, event=None):
        return self._dispatch_to_active_tab("on_alt_left", event)

    def _on_alt_right_key(self, event=None):
        return self._dispatch_to_active_tab("on_alt_right", event)

    def _on_ctrl_shift_d_key(self, event=None):
        return self._dispatch_to_active_tab("on_ctrl_shift_d", event)

    def _on_ctrl_shift_n_key(self, event=None):
        return self._dispatch_to_active_tab("on_ctrl_shift_n", event)

    def _on_f2_key(self, event=None):
        return self._dispatch_to_active_tab("on_f2", event)

    # ---- 탭 전환/창 생명주기 ----

    def on_tab_changed(self, event=None):
        """탭 전환 시: 방금 벗어난 탭에 on_deactivated()가 있으면 먼저 호출하고
        (컬렉션 탭은 이걸로 열려 있던 인라인 제목 편집을 커밋함), 방금 활성화된
        탭에 on_activated()가 있으면 호출한 뒤(달력메모 탭은 "오늘" 표시를 최신
        날짜로 다시 그림 - 자정 경과 대비) 상태표시줄을 갱신함."""
        active = self._active_tab()
        previous = self._last_active_tab
        if previous is not None and previous is not active:
            on_deactivated = getattr(previous, "on_deactivated", None)
            if on_deactivated:
                on_deactivated()
        self._last_active_tab = active
        on_activated = getattr(active, "on_activated", None)
        if on_activated:
            on_activated()
        self.update_status_bar()

    def _notify_holiday_problems(self):
        """holidays.json에서 형식이 맞지 않아 건너뛴 항목이 있으면 시작 후 한 번 안내함.
        (조용히 빠뜨리면 공휴일이 왜 안 보이는지 알기 어렵기 때문. 나머지 항목은 정상 사용됨)"""
        problems = getattr(self.store, "holiday_problems", [])
        if not problems:
            return
        shown = problems[:5]
        message = (f"holidays.json에서 형식이 맞지 않는 항목 {len(problems)}개를 건너뛰었습니다.\n"
                   "나머지 공휴일은 정상적으로 사용됩니다.\n\n· " + "\n· ".join(shown))
        if len(problems) > len(shown):
            message += f"\n· ... 외 {len(problems) - len(shown)}개"
        message += "\n\n날짜는 \"2026-09-25\"처럼 YYYY-MM-DD 형식으로, 이름은 문자열로 적어주세요."
        messagebox.showwarning("공휴일 파일 확인", message, parent=self.root)

    def _notify_load_problems(self):
        """시작할 때 데이터 파일(memos.json 등)을 정상으로 읽지 못했거나 일부를 건너뛰었다면 한 번
        안내함. 손상된 원본은 지우지 않고 같은 폴더에 보관해 두므로 거기서 복구할 수 있음."""
        problems = self.store.load_problems
        if not problems:
            return
        messagebox.showwarning(
            "데이터 파일 확인",
            "시작할 때 문제가 있었던 데이터 파일이 있습니다.\n\n" + "\n\n".join(problems),
            parent=self.root)

    def _reapply_theme_on_startup(self):
        """창이 완전히 표시된 뒤 테마를 다시 한번 적용해, 시작 시 일부 위젯이
        테마를 제대로 반영하지 못하는 렌더링 문제를 보정한다."""
        if sv_ttk:
            sv_ttk.set_theme(self.settings_mgr.theme_mode, self.root)
        apply_titlebar_theme(self.root, self.settings_mgr.theme_mode == "dark")
        self.apply_theme_colors()

    def restore_window_geometry(self):
        """창 위치와 크기를 복원"""
        geometry = self.settings_mgr.settings.get("window_geometry", "800x600+100+100")

        try:
            # geometry 문자열 검증: "800x600+100+100" 형식. 좌표는 -50처럼 음수(창이 화면
            # 왼쪽/위쪽 바깥에 걸쳐 있던 경우)일 수도 있어, '+' 문자 유무만 보면 "800x600-50-30"
            # 같은 유효한 값을 잘못된 것으로 판단함. 정규식으로 폭x높이와 +/- 부호가 붙은
            # x,y 좌표까지 정확히 확인함.
            if geometry and re.fullmatch(r"\d+x\d+[+-]\d+[+-]\d+", geometry):
                # UI 레이아웃 완료 대기
                self.root.update_idletasks()
                self.root.geometry(geometry)
                print(f"✅ 창 위치 복원: {geometry}")
            else:
                # 잘못된 형식이면 기본값 사용
                print(f"⚠️ 잘못된 geometry 형식: {geometry}")
                self.root.geometry("800x600+100+100")
        except Exception as e:
            print(f"❌ 창 위치 복원 실패: {e}")
            self.root.geometry("800x600+100+100")

        self.general_tab.restore_layout()
        self.checklist_tab.restore_layout()
        self.collection_tab.restore_layout()

    def on_closing(self):
        # 디바운스로 미뤄둔 저장이 있다면 취소하고(중복 저장 방지),
        # 아래에서 최신 상태를 바로 저장하므로 유실되는 내용은 없음
        self._cancel_pending_saves()
        # 컬렉션/체크리스트 탭에 열려 있는 인라인 편집이 있다면 커밋 후 저장하고,
        # 컬렉션의 백그라운드 제목 수집 폴링도 멈춤 (파괴된 위젯에 접근하는 예외 방지)
        self.collection_tab.on_deactivated()
        self.collection_tab._stop_polling()
        self.checklist_tab.on_deactivated()
        # 종료 전 설정 및 메모 저장 (창 크기, 위치 포함)
        # (저장에 실패하면 아래에서 한 번에 안내하므로, 개별 저장 실패 팝업은 띄우지 않음)
        memos_ok = self.save_memos(notify=False)
        calendar_ok = self.save_calendar_memos(notify=False)
        collections_ok = self.save_collections(notify=False)
        checklists_ok = self.save_checklists(notify=False)
        self.settings_mgr.save()
        if not (memos_ok and calendar_ok and collections_ok and checklists_ok):
            # 디스크 공간 부족/권한 문제 등으로 마지막 저장이 실패했는데도 그냥
            # 종료해버리면 방금 작성한 내용이 그대로 사라지므로, 사용자에게 알리고
            # 종료 여부를 직접 선택하게 함
            if not messagebox.askyesno(
                "저장 실패",
                "저장에 실패했습니다. 지금 종료하면 마지막으로 입력한 내용이\n"
                "저장되지 않을 수 있습니다. 그래도 종료하시겠습니까?",
                parent=self.root,
            ):
                return
        self.root.destroy()


if __name__ == "__main__":
    set_windows_app_id()  # 반드시 tk.Tk() 생성 전에 호출
    if not acquire_single_instance(get_app_dir()):
        notice_root = tk.Tk()
        notice_root.withdraw()
        messagebox.showwarning(
            "알파카 다이어리",
            "알파카 다이어리가 이미 실행 중입니다.\n작업표시줄에서 열려 있는 창을 확인해 주세요.",
            parent=notice_root)
        notice_root.destroy()
        sys.exit(0)
    root = tk.Tk()
    app = MemoApp(root)
    root.mainloop()
