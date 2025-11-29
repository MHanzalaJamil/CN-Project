import tkinter as tk
from tkinter import ttk, messagebox
import math
import random
from collections import defaultdict
import time
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import matplotlib
matplotlib.use('TkAgg')


class NetworkNode:
    def __init__(self, x, y, node_type, name):
        self.x = x
        self.y = y
        self.type = node_type  # 'cloud', 'router', 'switch', 'pc'
        self.name = name
        self.connections = []
        self.packets = []
        self.latency = random.randint(5, 50)
        self.throughput = random.randint(100, 1000)
        self.congestion = 0
        self.hop_count = 0  # NEW: Track hop count

    # NEW: Get congestion level category
    def get_congestion_level(self):
        """Returns congestion level: 'low', 'medium', 'high', 'critical'"""
        if self.congestion <= 1:
            return 'low'
        elif self.congestion <= 3:
            return 'medium'
        elif self.congestion <= 5:
            return 'high'
        else:
            return 'critical'
        
class Packet:
    def __init__(self, source, destination, path, packet_id=None):
        self.source = source
        self.destination = destination
        self.path = path
        self.current_index = 0
        self.progress = 0
        self.hop_count = len(path) - 1  # NEW: Calculate hops
        self.total_latency = 0  # NEW: Track cumulative latency
        self.timestamp = time.time()  # NEW: Packet creation time
        self.completed = False  # NEW: Track if packet reached destination
        self.packet_id = packet_id if packet_id else random.randint(1000, 9999)  # Unique packet ID
        
        # Congestion Control Attributes
        self.cwnd = 1  # Congestion window in MSS (Maximum Segment Size = 1500 bytes)
        self.ssthresh = 64  # Slow start threshold in MSS
        self.phase = "slow_start"  # Phases: slow_start, congestion_avoidance, fast_retransmit, fast_recovery
        self.dup_ack_count = 0  # Duplicate ACK counter
        self.rtt = 0  # Round trip time in milliseconds
        self.last_ack_time = time.time()  # Time of last ACK received
        self.bytes_sent = 0  # Total bytes sent
        self.bytes_acked = 0  # Total bytes acknowledged
        self.lost = False  # Whether packet was lost
        self.retransmitted = False  # Whether packet was retransmitted
        
        # Phase-based color scheme
        self.color = self.get_phase_color()
        
    def get_phase_color(self):
        """Return color based on current congestion control phase"""
        phase_colors = {
            "slow_start": "#28a745",          # Professional green
            "congestion_avoidance": "#0066cc", # Professional blue
            "fast_retransmit": "#ffc107",     # Amber
            "fast_recovery": "#fd7e14"        # Orange
        }
        return phase_colors.get(self.phase, "#ffffff")

    def set_phase(self, phase_name):
        """Helper to update packet phase and visual color"""
        self.phase = phase_name
        self.color = self.get_phase_color()
    
    def update_cwnd(self, algorithm="reno"):
        """Update congestion window based on current phase and algorithm"""
        if self.phase == "slow_start":
            # Exponentially increase: cwnd = cwnd * 2 on each successful ACK
            self.cwnd = min(self.cwnd * 2, self.ssthresh)
            if self.cwnd >= self.ssthresh:
                self.set_phase("congestion_avoidance")
        elif self.phase == "congestion_avoidance":
            # Linearly increase: cwnd = cwnd + 1/cwnd per RTT
            self.cwnd += 1.0 / max(self.cwnd, 1)
        elif self.phase == "fast_recovery":
            # Inflate cwnd by 1 for each duplicate ACK (Reno only)
            if algorithm == "reno":
                self.cwnd += 1
            # Tahoe doesn't have fast recovery, so this shouldn't happen

class CloudNetworkSimulator:
    def __init__(self, root):
        self.root = root
        self.root.title("Cloud Network Simulator - TCP Congestion Control Analytics")
        self.root.geometry("1920x1080")
        self.root.configure(bg="#0a0e27")
        
        # Try to maximize window
        try:
            self.root.state('zoomed')
        except:
            pass
        
        # Data structures
        self.nodes = []
        self.connections = []
        self.packets = []
        self.selected_node = None
        self.dragging_node = None
        self.connection_mode = False
        self.simulation_running = False
        self.highlighted_path = []  # NEW: Store path to highlight

        self.latency_history = []
        self.throughput_history = []
        self.time_stamps = []
        self.performance_start_time = time.time()

        self.traffic_load = "medium"  # Options: "light", "medium", "heavy"
        self.packet_generation_rate = 1000  # milliseconds
        
        # NEW: Manual Packet Mode
        self.manual_packet_mode = False
        self.manual_packets = []  # Store manually sent packets with details
        self.active_manual_packet_ids = set()  # Track which packets are from manual sends
        
        # Congestion Control Settings
        self.congestion_algorithm = "reno"  # Options: "reno", "tahoe"
        self.packet_loss_rate = 0.0  # Configurable packet loss rate (0-10%)
        self.learn_mode = False  # Learning mode with explanatory tooltips
        self.packet_counter = 0  # Global packet counter for unique IDs
        
        # Packet Timeline Tracking
        self.packet_events = []  # Store: {time, packet_id, cwnd, phase, rtt, event_type, throughput}
        self.manual_source_var = None
        self.manual_dest_var = None
        self.manual_source_dropdown = None
        self.manual_dest_dropdown = None
        self.manual_send_btn = None
        self.manual_packet_details = None  # NEW: Track manual packet details
        self.packet_details_timer = None
        self.debug_logging = True
        # Double-buffer / draw control
        self.redraw_scheduled = False
        self.last_draw_time = 0
        self.min_draw_interval = 0.1  # seconds (100ms)

        # Topology/layout
        self.topology_margin = 80

        # Performance controls
        self.max_packets = 50
        self.performance_mode = False

         # NEW: Routing Analysis Variables
        self.routing_stats = {
            'total_packets': 0,
            'avg_hop_count': 0,
            'min_hops': float('inf'),
            'max_hops': 0,
            'path_history': []
        }
        
        # Professional light theme palette
        self.colors = {
            # Backgrounds
            'bg': '#f8f9fa',
            'bg_secondary': '#ffffff',
            'surface': '#ffffff',
            'surface_hover': '#e9ecef',
            'panel_bg': '#f8f9fa',
            'canvas_bg': '#f1f3f5',
            'border': '#dee2e6',

            # Accents
            'accent': '#0066cc',
            'accent_dark': '#004c99',
            'accent_secondary': '#6c757d',

            # Typography
            'text': '#212529',
            'text_secondary': '#6c757d',
            'text_muted': '#adb5bd',

            # Status
            'success': '#28a745',
            'warning': '#ffc107',
            'error': '#dc3545',

            # Node colors
            'cloud': '#0066cc',
            'router': '#6610f2',
            'switch': '#e83e8c',
            'pc': '#28a745',

            # Phase colors
            'phase_slow_start': '#28a745',
            'phase_congestion_avoid': '#0066cc',
            'phase_fast_retransmit': '#ffc107',
            'phase_fast_recovery': '#fd7e14',
        }

        # Standard fonts
        self.fonts = {
            'title': ("Segoe UI", 18, "bold"),
            'subtitle': ("Segoe UI", 12),
            'section': ("Segoe UI", 12, "bold"),
            'body': ("Segoe UI", 10),
            'body_bold': ("Segoe UI", 10, "bold"),
            'mono': ("Consolas", 10),
            'metric': ("Courier New", 11, "bold")
        }

        # Phase definitions referencing palette
        self.phase_definitions = {
            "slow_start": {
                "name": "Slow Start",
                "color": self.colors['phase_slow_start'],
                "desc": "cwnd doubles every RTT until it reaches ssthresh."
            },
            "congestion_avoidance": {
                "name": "Congestion Avoidance",
                "color": self.colors['phase_congestion_avoid'],
                "desc": "cwnd grows linearly (additive increase) per RTT."
            },
            "fast_retransmit": {
                "name": "Fast Retransmit",
                "color": self.colors['phase_fast_retransmit'],
                "desc": "Triggered by 3 duplicate ACKs; resend segment immediately."
            },
            "fast_recovery": {
                "name": "Fast Recovery",
                "color": self.colors['phase_fast_recovery'],
                "desc": "Temporarily inflates cwnd to keep pipeline full after retransmit."
            }
        }

        # Apply global background
        self.root.configure(bg=self.colors['bg'])
        
        self.setup_ui()
        
    def setup_ui(self):
        """Modern responsive UI with focus on topology visualization"""
        # Get screen size for responsiveness
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        
        # ===== TOP NAVIGATION BAR =====
        nav_bar = tk.Frame(
            self.root,
            bg=self.colors['bg_secondary'],
            height=70,
            highlightbackground=self.colors['border'],
            highlightthickness=1
        )
        nav_bar.pack(side=tk.TOP, fill=tk.X, padx=0, pady=0)
        nav_bar.pack_propagate(False)
        
        # Title section
        title_frame = tk.Frame(nav_bar, bg=self.colors['bg_secondary'])
        title_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=25, pady=15)
        
        tk.Label(
            title_frame,
            text="🌐 Network Simulator",
            font=("Segoe UI", 20, "bold"),
            bg=self.colors['bg_secondary'],
            fg=self.colors['text']
        ).pack(anchor='w')
        tk.Label(
            title_frame,
            text="TCP Congestion Control Analysis",
            font=("Segoe UI", 11),
            bg=self.colors['bg_secondary'],
            fg=self.colors['text_secondary']
        ).pack(anchor='w')
        
        # Control buttons
        btn_frame = tk.Frame(nav_bar, bg=self.colors['bg_secondary'])
        btn_frame.pack(side=tk.RIGHT, padx=25, pady=15)
        
        self.sim_button = self.create_button(btn_frame, "▶ Simulate", self.toggle_simulation, self.colors['accent'])
        self.sim_button.pack(side=tk.LEFT, padx=8)
        
        self.create_button(btn_frame, "📊 Metrics", self.show_metrics, self.colors['accent_secondary']).pack(side=tk.LEFT, padx=8)
        self.create_button(btn_frame, "📈 Graphs", self.show_performance_graphs, self.colors['success']).pack(side=tk.LEFT, padx=8)
        self.create_button(btn_frame, "🔄 Reset", self.reset_network, self.colors['error']).pack(side=tk.LEFT, padx=8)
        
        # ===== MAIN CONTENT AREA =====
        main_container = tk.Frame(self.root, bg=self.colors['bg'])
        main_container.pack(fill=tk.BOTH, expand=True, padx=15, pady=15)
        
        # LEFT PANEL - Network Setup
        left_panel = tk.Frame(
            main_container,
            bg=self.colors['surface'],
            relief=tk.FLAT,
            bd=0,
            highlightbackground=self.colors['border'],
            highlightthickness=1
        )
        left_panel.pack(side=tk.LEFT, fill=tk.BOTH, padx=(0, 12))
        left_panel.pack_propagate(False)
        left_panel.configure(width=300)
        
        self._create_setup_panel(left_panel)
        
        # CENTER PANEL - Canvas (Primary Focus)
        center_frame = tk.Frame(main_container, bg=self.colors['surface'], relief=tk.FLAT, bd=0)
        center_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 12))
        
        # Canvas title
        canvas_title_frame = tk.Frame(
            center_frame,
            bg=self.colors['bg_secondary'],
            height=45,
            highlightbackground=self.colors['border'],
            highlightthickness=1
        )
        canvas_title_frame.pack(fill=tk.X, padx=0, pady=0)
        canvas_title_frame.pack_propagate(False)
        
        tk.Label(
            canvas_title_frame,
            text="Network Topology",
            font=("Segoe UI", 13, "bold"),
            bg=self.colors['bg_secondary'],
            fg=self.colors['text']
        ).pack(side=tk.LEFT, padx=15, pady=12)
        
        # Canvas container
        canvas_container = tk.Frame(center_frame, bg=self.colors['canvas_bg'], highlightbackground=self.colors['border'], highlightthickness=1)
        canvas_container.pack(fill=tk.BOTH, expand=True, padx=0, pady=0)
        
        self.canvas = tk.Canvas(
            canvas_container,
            bg=self.colors['canvas_bg'],
            highlightthickness=0,
            cursor="crosshair"
        )
        self.canvas.pack(fill=tk.BOTH, expand=True)
        
        # Canvas bindings
        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.canvas.bind("<B1-Motion>", self.on_canvas_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_canvas_release)
        self.canvas.bind("<Button-3>", self.on_right_click)
        self.canvas.bind("<Motion>", self.on_canvas_motion)
        self.canvas.bind("<Leave>", self.on_canvas_leave)
        
        # RIGHT PANEL - Packet Details (Only visible in manual mode)
        right_panel = tk.Frame(
            main_container,
            bg=self.colors['surface'],
            relief=tk.FLAT,
            bd=0,
            highlightbackground=self.colors['border'],
            highlightthickness=1
        )
        right_panel.pack(side=tk.LEFT, fill=tk.BOTH, padx=0)
        right_panel.pack_propagate(False)
        right_panel.configure(width=280)
        
        self.right_panel_ref = right_panel  # Store reference for toggling visibility
        self._create_packet_details_panel(right_panel)
        
        # ===== STATUS BAR =====
        status_bar = tk.Frame(
            self.root,
            bg=self.colors['bg_secondary'],
            height=45,
            highlightbackground=self.colors['border'],
            highlightthickness=1
        )
        status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        status_bar.pack_propagate(False)
        
        self.status_label = tk.Label(
            status_bar,
            text="Ready",
            bg=self.colors['bg_secondary'],
            fg=self.colors['text_secondary'],
            font=("Segoe UI", 10)
        )
        self.status_label.pack(side=tk.LEFT, padx=20, pady=10)
        
        # Tooltip
        self.tooltip_window = None
        self.status_update_timer = None
        
        self.populate_node_options()
    
    def _create_setup_panel(self, parent):
        """Create network setup panel"""
        # Scrollable area
        canvas = tk.Canvas(parent, bg=self.colors['surface'], highlightthickness=0)
        scrollbar = tk.Scrollbar(parent, orient="vertical", command=canvas.yview)
        scrollable = tk.Frame(canvas, bg=self.colors['surface'])
        
        scrollable.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=scrollable, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
        def on_scroll(event):
            widget = canvas.winfo_containing(event.x_root, event.y_root)
            if widget is not None and widget in (canvas, scrollable):
                canvas.yview_scroll(int(-1*(event.delta/120)), "units")

        canvas.bind("<MouseWheel>", on_scroll)
        scrollable.bind("<MouseWheel>", on_scroll)
        
        # Section: Add Nodes
        self._add_section_title(scrollable, "Create Nodes")
        node_types = [("☁ Cloud", "cloud", self.colors['cloud']),
            ("⚡ Router", "router", self.colors['router']),
            ("⊞ Switch", "switch", self.colors['switch']),
                     ("💻 PC", "pc", self.colors['pc'])]
        
        for label, ntype, color in node_types:
            btn = tk.Button(
                scrollable,
                text=label,
                          command=lambda t=ntype: self.add_node(t),
                bg=color,
                fg="white",
                font=("Segoe UI", 9, "bold"),
                relief=tk.FLAT,
                cursor="hand2",
                padx=10,
                pady=8,
                activebackground=self.darken_color(color),
                activeforeground="white",
                borderwidth=0
            )
            btn.pack(pady=3, padx=8, fill=tk.X)
        
        self.conn_button = tk.Button(
            scrollable,
            text="🔗 Connect",
                                     command=self.toggle_connection_mode,
            bg=self.colors['accent_secondary'],
            fg="white",
            font=("Segoe UI", 9, "bold"),
            relief=tk.FLAT,
            padx=10,
            pady=8,
            activebackground=self.darken_color(self.colors['accent_secondary']),
            borderwidth=0
        )
        self.conn_button.pack(pady=10, padx=8, fill=tk.X)
        
        # Section: Topology builder
        self._add_section_title(scrollable, "Topology Builder")
        tk.Label(
            scrollable,
            text="Generate a full network tree automatically.",
            bg=self.colors['surface'],
            fg=self.colors['text_secondary'],
            font=("Segoe UI", 9),
            wraplength=240,
            justify=tk.LEFT
        ).pack(anchor='w', padx=10, pady=(0, 8))
        self.create_button(
            scrollable,
            "🌳 Build Topology",
            self.build_random_topology,
            self.colors['accent']
        ).pack(pady=5, padx=8, fill=tk.X)
        
        # Section: Traffic Load
        self._add_section_title(scrollable, "Traffic Load")
        self.traffic_buttons = {}
        for label, load, color in [
            ("🟢 Light", "light", self.colors['success']),
            ("🟡 Medium", "medium", self.colors['warning']),
            ("🔴 Heavy", "heavy", self.colors['error'])
        ]:
            btn = tk.Button(
                scrollable,
                text=label,
                          command=lambda l=load: self.set_traffic_load(l),
                bg=self.colors['surface_hover'],
                fg=self.colors['text'],
                font=("Segoe UI", 8),
                relief=tk.FLAT,
                padx=10,
                pady=6,
                activebackground=self.darken_color(self.colors['surface_hover']),
                borderwidth=0
            )
            btn.pack(pady=2, padx=8, fill=tk.X)
            self.traffic_buttons[load] = btn
            if load == "medium":
                btn.config(bg=color, fg="white")
        
        # Section: Manual Packet
        self._add_section_title(scrollable, "Manual Packet Send")
        tk.Label(scrollable, text="Source:", bg=self.colors['surface'], fg=self.colors['text_secondary'],
                font=("Segoe UI", 8)).pack(anchor='w', padx=10, pady=(5, 2))
        self.manual_source_var = tk.StringVar()
        self.manual_source_dropdown = ttk.Combobox(scrollable, textvariable=self.manual_source_var,
                                                   state='readonly', width=30)
        self.manual_source_dropdown.pack(padx=8, pady=2, fill=tk.X)
        
        tk.Label(scrollable, text="Destination:", bg=self.colors['surface'], fg=self.colors['text_secondary'],
                font=("Segoe UI", 8)).pack(anchor='w', padx=10, pady=(8, 2))
        self.manual_dest_var = tk.StringVar()
        self.manual_dest_dropdown = ttk.Combobox(scrollable, textvariable=self.manual_dest_var,
                                                 state='readonly', width=30)
        self.manual_dest_dropdown.pack(padx=8, pady=2, fill=tk.X)
        
        self.manual_send_btn = tk.Button(
            scrollable,
            text="🚀 Send Packet",
            command=self.send_manual_packet,
            bg=self.colors['accent'],
            fg="white",
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            padx=10,
            pady=10,
            activebackground=self.darken_color(self.colors['accent']),
            borderwidth=0
        )
        self.manual_send_btn.pack(padx=8, pady=12, fill=tk.X)
        
        # Section: Statistics
        self._add_section_title(scrollable, "Live Stats")
        self.stats_text = tk.Label(
            scrollable,
            text="Packets: 0\nAlgo: Reno\nLoss: 0%",
            bg=self.colors['surface'],
            fg=self.colors['text_secondary'],
            font=("Consolas", 9),
            justify=tk.LEFT
        )
        self.stats_text.pack(padx=8, pady=8, fill=tk.X)
    
    def _add_section_title(self, parent, text):
        """Add a section title with separator"""
        tk.Label(
            parent,
            text=text,
            font=("Segoe UI", 11, "bold"),
            bg=self.colors['surface'],
            fg=self.colors['text']
        ).pack(anchor='w', padx=10, pady=(12, 5))
        tk.Frame(parent, bg=self.colors['border'], height=1).pack(fill=tk.X, padx=8, pady=3)
    
    def _create_packet_details_panel(self, parent):
        """Create detailed packet information panel"""
        title = tk.Label(parent, text="📊 Packet Analysis", font=("Segoe UI", 11, "bold"),
                        bg=self.colors['surface'], fg=self.colors['accent'])
        title.pack(fill=tk.X, padx=12, pady=10)
        
        tk.Frame(parent, bg=self.colors['border'], height=1).pack(fill=tk.X, padx=12, pady=5)
        
        # Scrollable packet details
        canvas = tk.Canvas(parent, bg=self.colors['surface'], highlightthickness=0)
        scrollbar = tk.Scrollbar(parent, orient="vertical", command=canvas.yview, bg=self.colors['surface'])
        self.packet_details_frame = tk.Frame(canvas, bg=self.colors['surface'])
        
        self.packet_details_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=self.packet_details_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas.pack(side="left", fill="both", expand=True, padx=10, pady=10)
        scrollbar.pack(side="right", fill="y")
        
        # Initial message
        tk.Label(self.packet_details_frame, text="Send a packet to see details", 
                bg=self.colors['surface'], fg=self.colors['text_secondary'],
                font=("Segoe UI", 10, "italic")).pack(pady=30, padx=10)
        
    def create_button(self, parent, text, command, color):
        """Create a styled button with consistent hover behavior"""
        btn = tk.Button(
            parent,
            text=text,
            command=command,
            bg=color,
            fg="white",
            font=("Segoe UI", 9, "bold"),
            relief=tk.FLAT,
            cursor="hand2",
            padx=12,
            pady=7,
            borderwidth=0,
            activebackground=self.darken_color(color),
            activeforeground="white"
        )

        def on_enter(_):
            btn.configure(bg=self.darken_color(color))

        def on_leave(_):
            btn.configure(bg=color)

        btn.bind("<Enter>", on_enter)
        btn.bind("<Leave>", on_leave)
        return btn
    
    def lighten_color(self, color, factor=0.15):
        """Lighten a hex color by given factor"""
        color = color.lstrip('#')
        r, g, b = tuple(int(color[i:i+2], 16) for i in (0, 2, 4))
        r = min(255, int(r + (255 - r) * factor))
        g = min(255, int(g + (255 - g) * factor))
        b = min(255, int(b + (255 - b) * factor))
        return f'#{r:02x}{g:02x}{b:02x}'

    def darken_color(self, color, factor=0.15):
        """Darken a hex color by given factor"""
        color = color.lstrip('#')
        r, g, b = tuple(int(color[i:i+2], 16) for i in (0, 2, 4))
        r = max(0, int(r * (1 - factor)))
        g = max(0, int(g * (1 - factor)))
        b = max(0, int(b * (1 - factor)))
        return f'#{r:02x}{g:02x}{b:02x}'
    
    def log_debug(self, *args):
        if self.debug_logging:
            print("[DEBUG]", *args)

    def _style_axes(self, axes):
        """Apply light theme styling to matplotlib axes"""
        if not isinstance(axes, (list, tuple)):
            axes = [axes]
        for ax in axes:
            ax.set_facecolor(self.colors['panel_bg'])
            ax.tick_params(colors=self.colors['text'])
            ax.xaxis.label.set_color(self.colors['text_secondary'])
            ax.yaxis.label.set_color(self.colors['text_secondary'])
            ax.title.set_color(self.colors['text'])
            ax.grid(True, alpha=0.5, color=self.colors['border'])
            for spine in ax.spines.values():
                spine.set_color(self.colors['border'])
            legend = ax.get_legend()
            if legend:
                legend.get_frame().set_facecolor(self.colors['surface'])
                legend.get_frame().set_edgecolor(self.colors['border'])
                for text in legend.get_texts():
                    text.set_color(self.colors['text'])

    def show_learning_tooltip(self, title, message):
        """Display contextual learning tooltip when learn mode is active"""
        if not self.learn_mode:
            return
        
        learn_window = tk.Toplevel(self.root)
        learn_window.title(title)
        learn_window.configure(bg=self.colors['surface'])
        learn_window.geometry("400x250")
        
        # Center overlay
        learn_window.update_idletasks()
        x = (self.root.winfo_screenwidth() // 2) - 200
        y = (self.root.winfo_screenheight() // 2) - 125
        learn_window.geometry(f"+{x}+{y}")
        
        tk.Label(
            learn_window,
            text=f"📚 {title}",
            font=("Segoe UI", 13, "bold"),
            bg=self.colors['surface'],
            fg=self.colors['accent']
        ).pack(pady=15)
        
        tk.Label(
            learn_window,
            text=message,
            font=("Segoe UI", 10),
            bg=self.colors['surface'],
            fg=self.colors['text'],
            justify=tk.LEFT,
            wraplength=350
        ).pack(padx=20, pady=10)
        
        tk.Button(
            learn_window,
            text="Got it!",
            command=learn_window.destroy,
            bg=self.colors['accent'],
            fg="white",
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            padx=20,
            pady=6
        ).pack(pady=10)
        
        learn_window.after(5000, learn_window.destroy)
    
    # === TOPOLOGY GENERATION METHODS ===
    def generate_topology(self, topology_type):

        self.reset_network(confirm=False)
        
        if topology_type == "star":
            self.create_star_topology()
        elif topology_type == "mesh":
            self.create_mesh_topology()
        elif topology_type == "ring":
            self.create_ring_topology()
        elif topology_type == "tree":
            self.create_tree_topology()
        elif topology_type == "linear":
            self.create_linear_topology()
            
        self.draw_network()
        self.status_label.config(text=f"{topology_type.upper()} topology created with {len(self.nodes)} nodes")
        self.populate_node_options()
        
    # NEW: Update Packet Details Panel in Real-time
    def update_packet_details(self):
        """Update the right panel with active packet details"""
        # Clear existing widgets
        for widget in self.packet_details_frame.winfo_children():
            widget.destroy()
        
        if not self.packets:
            tk.Label(
                self.packet_details_frame,
                text="No active packets",
                bg=self.colors['surface'],
                fg=self.colors['text_secondary'],
                font=("Segoe UI", 10, "italic")
            ).pack(pady=25, padx=10)
            return
        
        # Display each active packet
        for i, packet in enumerate(self.packets[:15]):  # Show max 15 packets
            card = tk.Frame(
                self.packet_details_frame,
                bg=self.colors['surface'],
                highlightbackground=self.colors['border'],
                highlightthickness=1,
                bd=0
            )
            card.pack(fill=tk.X, padx=8, pady=6)

            header_text = f"Packet {packet.packet_id}  •  {packet.source.name} → {packet.destination.name}"
            tk.Label(
                card,
                text=header_text,
                bg=self.colors['surface'],
                fg=self.colors['text'],
                font=("Segoe UI", 10, "bold")
            ).pack(anchor='w', padx=12, pady=(10, 4))

            separator = tk.Frame(card, bg=self.colors['border'], height=1)
            separator.pack(fill=tk.X, padx=12, pady=(0, 8))

            info_frame = tk.Frame(card, bg=self.colors['surface'])
            info_frame.pack(fill=tk.BOTH, expand=True, padx=12, pady=5)

            stats = [
                ("Phase", packet.phase.replace('_', ' ').title(), packet.color),
                ("cwnd", f"{packet.cwnd:.1f} MSS", self.colors['accent']),
                ("RTT", f"{packet.rtt:.1f} ms", self.colors['warning']),
                ("Hops Rem.", str(len(packet.path) - packet.current_index - 1), self.colors['text_secondary']),
                ("Status", "Delivered" if packet.completed else ("Lost" if packet.lost else "In Transit"),
                 self.colors['success'] if packet.completed else (self.colors['error'] if packet.lost else self.colors['warning']))
            ]

            for label, value, color in stats:
                row = tk.Frame(info_frame, bg=self.colors['surface'])
                row.pack(fill=tk.X, pady=2)
                tk.Label(
                    row,
                    text=f"{label}:",
                    bg=self.colors['surface'],
                    fg=self.colors['text_secondary'],
                    font=("Segoe UI", 9)
                ).pack(side=tk.LEFT)
                tk.Label(
                    row,
                    text=value,
                    bg=self.colors['surface'],
                    fg=color,
                    font=("Segoe UI", 9, "bold")
                ).pack(side=tk.RIGHT)

            progress_pct = min(100, int((packet.current_index + packet.progress) / len(packet.path) * 100))
            progress_frame = tk.Frame(card, bg=self.colors['surface'])
            progress_frame.pack(fill=tk.X, padx=12, pady=(8, 10))

            progress_canvas = tk.Canvas(progress_frame, height=12, bg=self.colors['panel_bg'], highlightthickness=0, width=200)
            progress_canvas.pack(fill=tk.X)
            max_width = 200
            bar_width = int(progress_pct / 100 * max_width)
            progress_canvas.create_rectangle(0, 0, bar_width, 12, fill=packet.color, outline="")
            progress_canvas.create_text(
                max_width / 2,
                6,
                text=f"{progress_pct}%",
                fill=self.colors['text_secondary'],
                font=("Segoe UI", 8, "bold")
            )
        
        if len(self.packets) > 15:
            tk.Label(
                self.packet_details_frame,
                text=f"... and {len(self.packets) - 15} more packets",
                bg=self.colors['surface'],
                fg=self.colors['text_secondary'],
                font=("Segoe UI", 9, "italic")
            ).pack(pady=12)

    def stop_packet_details_updates(self):
        """Stop scheduled packet detail refresh"""
        if self.packet_details_timer:
            self.root.after_cancel(self.packet_details_timer)
            self.packet_details_timer = None

    def schedule_packet_details_updates(self):
        """Begin periodic packet detail refresh loop"""
        self.stop_packet_details_updates()

        def loop():
            if self.manual_packet_mode:
                self.update_manual_packet_display()
            else:
                self.update_packet_details()
            if self.simulation_running or self.manual_packet_mode:
                self.packet_details_timer = self.root.after(300, loop)
            else:
                self.packet_details_timer = None

        loop()
    
    # === NEW: TOPOLOGY GENERATION METHODS ===
    def generate_topology(self, topology_type):
        self.reset_network(confirm=False)

        # Ensure canvas is ready
        try:
            self.canvas.update_idletasks()
        except Exception:
            pass

        if topology_type == "star":
            self.create_star_topology()
        elif topology_type == "mesh":
            self.create_mesh_topology()
        elif topology_type == "ring":
            self.create_ring_topology()
        elif topology_type == "tree":
            self.create_tree_topology()
        elif topology_type == "linear":
            self.create_linear_topology()

        # Scale to fit canvas
        try:
            self.scale_topology_to_canvas()
        except Exception:
            pass

        self.draw_network()
        self.status_label.config(text=f"{topology_type.upper()} topology created with {len(self.nodes)} nodes")
        self.populate_node_options()
    

    # NEW: Set Traffic Load Level
    def set_traffic_load(self, load_level):
        """Change network traffic load: light, medium, or heavy"""
        self.traffic_load = load_level
        
        # Update packet generation rate based on load
        if load_level == "light":
            self.packet_generation_rate = 2000  # 2 seconds
            load_color = self.colors['success']
            self.performance_mode = False
            self.max_packets = 50
        elif load_level == "medium":
            self.packet_generation_rate = 1000  # 1 second
            load_color = self.colors['warning']
            self.performance_mode = False
            self.max_packets = 80
        else:  # heavy
            self.packet_generation_rate = 300  # 0.3 seconds
            load_color = self.colors['error']
            # Enable performance optimizations
            self.performance_mode = True
            self.max_packets = 50
            try:
                messagebox.showinfo("Performance Mode",
                                    "Heavy traffic enabled — performance mode active.\n" +
                                    "Visual updates reduced and packet limit enforced.")
            except Exception:
                pass
        
        # Update button colors
        for load, btn in self.traffic_buttons.items():
            if load == load_level:
                btn.config(bg=load_color, fg="white")
            else:
                btn.config(bg=self.colors['surface_hover'], fg=self.colors['text'])
        
        self.status_label.config(text=f"Traffic load set to: {load_level.upper()}")
    
    # NEW: Set Congestion Control Algorithm
    def set_congestion_algorithm(self, algorithm):
        """Change congestion control algorithm: reno or tahoe"""
        self.congestion_algorithm = algorithm
        self.status_label.config(text=f"Congestion algorithm set to: TCP {algorithm.upper()}")
        self.update_real_time_stats()
    
    # NEW: Populate manual source/destination dropdowns
    def populate_node_options(self):
        """Refresh manual packet dropdowns with the current node list"""
        if not self.manual_source_dropdown or not self.manual_dest_dropdown:
            return
        
        node_names = [node.name for node in self.nodes]
        self.manual_source_dropdown['values'] = node_names
        self.manual_dest_dropdown['values'] = node_names
        
        # Preserve selections if possible
        if self.manual_source_var.get() not in node_names:
            self.manual_source_var.set(node_names[0] if node_names else "")
        if self.manual_dest_var.get() not in node_names:
            self.manual_dest_var.set(node_names[1] if len(node_names) > 1 else "")
        
        # Disable manual send if fewer than 2 nodes
        if self.manual_send_btn:
            state = tk.NORMAL if len(node_names) >= 2 else tk.DISABLED
            self.manual_send_btn.config(state=state)
    
    # NEW: Update Real-time Statistics
    def update_real_time_stats(self):
        """Update real-time statistics panel"""
        if not hasattr(self, 'stats_text'):
            return
        
        active_packets = len(self.packets)
        if active_packets > 0:
            avg_cwnd = sum(p.cwnd for p in self.packets) / active_packets
            lost_packets = sum(1 for p in self.packets if p.lost)
            loss_rate = (lost_packets / max(active_packets, 1)) * 100
        else:
            avg_cwnd = 0
            loss_rate = 0
        
        algo_name = "Reno" if self.congestion_algorithm == "reno" else "Tahoe"
        phase_counts = self.get_phase_counts()
        stats = (
            f"Algorithm: {algo_name}\n"
            f"Active Packets: {active_packets}\n"
            f"Avg cwnd: {avg_cwnd:.1f} MSS\n"
            f"Loss Rate: {loss_rate:.1f}%\n"
            f"Phases → SS:{phase_counts['slow_start']}  CA:{phase_counts['congestion_avoidance']}\n"
            f"            FRx:{phase_counts['fast_retransmit']}  FRec:{phase_counts['fast_recovery']}"
        )
        self.stats_text.config(text=stats)
    
    def get_phase_counts(self):
        """Return counts of packets per TCP phase"""
        counts = {
            "slow_start": 0,
            "congestion_avoidance": 0,
            "fast_retransmit": 0,
            "fast_recovery": 0
        }
        for packet in self.packets:
            if packet.phase in counts:
                counts[packet.phase] += 1
        return counts
    
    # NEW: Handle Congestion Control for Packet
    def handle_congestion_control(self, packet, current_node):
        """Apply congestion control algorithm logic based on node congestion"""
        current_time = time.time()
        base_rtt = current_node.latency
        congestion_delay = current_node.congestion * 5  # 5ms delay per congestion unit
        packet.rtt = base_rtt + congestion_delay
        
        # CASE 1: Severe congestion -> timeout
        if current_node.congestion > 9:
            if self.congestion_algorithm == "reno":
                self.handle_timeout_reno(packet)
            else:
                self.handle_timeout_tahoe(packet)
            packet.dup_ack_count = 0
            self.record_packet_event(packet, "timeout")
            return
        
        # CASE 2: High congestion -> duplicate ACKs (Fast Retransmit trigger)
        if current_node.congestion > 7:
            packet.dup_ack_count += 1
            if packet.dup_ack_count >= 3:
                if self.congestion_algorithm == "reno":
                    self.handle_fast_retransmit_reno(packet)
                else:
                    self.handle_fast_retransmit_tahoe(packet)
                self.record_packet_event(packet, "fast_retransmit")
            return
        
        # CASE 3: Fast Recovery inflation (Reno only)
        if current_node.congestion > 5 and packet.phase == "fast_recovery" and self.congestion_algorithm == "reno":
            packet.cwnd += 1
            self.record_packet_event(packet, "cwnd_inflation")
            return
        
        # CASE 4: Normal ACK path
        packet.last_ack_time = current_time
        packet.dup_ack_count = 0
        
        if packet.phase == "fast_recovery" and self.congestion_algorithm == "reno":
            packet.cwnd = packet.ssthresh
            packet.set_phase("congestion_avoidance")
            self.record_packet_event(packet, "exit_fast_recovery")
        else:
            previous_cwnd = packet.cwnd
            packet.update_cwnd(self.congestion_algorithm)
            if previous_cwnd < packet.ssthresh <= packet.cwnd:
                packet.set_phase("congestion_avoidance")
                self.record_packet_event(packet, "phase_transition_CA")
        
        self.record_packet_event(packet, "ack_received")
    
    # NEW: Handle Fast Retransmit for TCP Reno
    def handle_fast_retransmit_reno(self, packet):
        """TCP Reno: Fast Retransmit and Fast Recovery"""
        packet.set_phase("fast_retransmit")
        packet.ssthresh = max(packet.cwnd / 2, 2)
        packet.cwnd = packet.ssthresh + 3
        packet.set_phase("fast_recovery")
        packet.retransmitted = True
        packet.dup_ack_count = 0
        
        self.show_learning_tooltip(
            "TCP Reno Fast Retransmit",
            f"3 duplicate ACKs detected.\n"
            f"ssthresh = {packet.ssthresh:.1f} MSS\n"
            f"cwnd = ssthresh + 3 = {packet.cwnd:.1f} MSS\n"
            f"Entering Fast Recovery."
        )
    
    # NEW: Handle Fast Retransmit for TCP Tahoe
    def handle_fast_retransmit_tahoe(self, packet):
        """TCP Tahoe: Fast Retransmit only (no Fast Recovery)"""
        packet.set_phase("fast_retransmit")
        packet.ssthresh = max(packet.cwnd / 2, 2)
        packet.cwnd = 1  # Reset to slow start
        packet.set_phase("slow_start")
        packet.retransmitted = True
        packet.dup_ack_count = 0
        
        self.show_learning_tooltip(
            "TCP Tahoe Fast Retransmit",
            f"Packet loss detected.\n"
            f"ssthresh = {packet.ssthresh:.1f} MSS\n"
            f"cwnd reset to 1 MSS.\n"
            f"Returning to Slow Start."
        )
    
    # NEW: Handle Timeout for TCP Reno
    def handle_timeout_reno(self, packet):
        """TCP Reno: Timeout handling"""
        packet.ssthresh = max(packet.cwnd / 2, 2)
        packet.cwnd = 1
        packet.set_phase("slow_start")
        packet.lost = True
        packet.dup_ack_count = 0
        
        self.show_learning_tooltip(
            "TCP Reno Timeout",
            f"Timeout detected.\n"
            f"ssthresh = {packet.ssthresh:.1f} MSS\n"
            f"cwnd reset to 1 MSS.\n"
            f"Restarting Slow Start."
        )
    
    # NEW: Handle Timeout for TCP Tahoe
    def handle_timeout_tahoe(self, packet):
        """TCP Tahoe: Timeout handling"""
        packet.ssthresh = max(packet.cwnd / 2, 2)
        packet.cwnd = 1
        packet.set_phase("slow_start")
        packet.lost = True
        packet.dup_ack_count = 0
        
        self.show_learning_tooltip(
            "TCP Tahoe Timeout",
            f"Timeout detected.\n"
            f"ssthresh = {packet.ssthresh:.1f} MSS\n"
            f"cwnd reset to 1 MSS.\n"
            f"Returning to Slow Start."
        )
    
    # NEW: Record Packet Event for Timeline
    def record_packet_event(self, packet, event_type):
        """Record packet event for timeline analysis (throttled).

        Only record important events or sample a fraction to avoid flooding.
        """
        current_time = time.time() - self.performance_start_time

        important_events = {"created", "delivered", "dropped", "timeout", "fast_retransmit", "exit_fast_recovery", "manual_created"}

        # Sample less-important events
        if event_type not in important_events and random.random() > 0.10:
            return

        # Calculate throughput (simplified)
        if packet.rtt > 0:
            throughput = (packet.cwnd * 1500 * 8) / (packet.rtt / 1000) / 1000000  # Mbps
        else:
            throughput = 0

        event = {
            'time': current_time,
            'packet_id': packet.packet_id,
            'cwnd': packet.cwnd,
            'phase': packet.phase,
            'rtt': packet.rtt,
            'event_type': event_type,
            'throughput': throughput,
            'node_congestion': packet.path[packet.current_index].congestion if packet.current_index < len(packet.path) else 0
        }
        self.packet_events.append(event)

        # Keep only last 500 events to limit memory
        if len(self.packet_events) > 500:
            self.packet_events = self.packet_events[-500:]

    def create_star_topology(self):
        """Star topology: central router with multiple PCs"""
        center_x, center_y = 600, 400
        
        # Central router
        router = NetworkNode(center_x, center_y, "router", "ROUTER1")
        self.nodes.append(router)
        
        # Create PCs in a circle around router
        num_pcs = 6
        radius = 200
        for i in range(num_pcs):
            angle = (2 * math.pi * i) / num_pcs
            x = center_x + radius * math.cos(angle)
            y = center_y + radius * math.sin(angle)
            
            pc = NetworkNode(x, y, "pc", f"PC{i+1}")
            self.nodes.append(pc)
            
            # Connect to router
            router.connections.append(pc)
            pc.connections.append(router)
            self.connections.append((router, pc))
    
    def create_mesh_topology(self):
        """Mesh topology: all nodes connected to all other nodes"""
        positions = [
            (400, 250), (600, 250), (800, 250),
            (400, 450), (600, 450), (800, 450)
        ]
        
        # Create routers
        for i, (x, y) in enumerate(positions):
            router = NetworkNode(x, y, "router", f"ROUTER{i+1}")
            self.nodes.append(router)
        
        # Connect all to all
        for i, node1 in enumerate(self.nodes):
            for node2 in self.nodes[i+1:]:
                node1.connections.append(node2)
                node2.connections.append(node1)
                self.connections.append((node1, node2))
    
    def create_ring_topology(self):
        """Ring topology: nodes connected in a circle"""
        center_x, center_y = 600, 400
        num_nodes = 8
        radius = 220
        
        for i in range(num_nodes):
            angle = (2 * math.pi * i) / num_nodes
            x = center_x + radius * math.cos(angle)
            y = center_y + radius * math.sin(angle)
            
            node = NetworkNode(x, y, "router", f"ROUTER{i+1}")
            self.nodes.append(node)
        
        # Connect in ring
        for i in range(len(self.nodes)):
            node1 = self.nodes[i]
            node2 = self.nodes[(i + 1) % len(self.nodes)]
            
            node1.connections.append(node2)
            node2.connections.append(node1)
            self.connections.append((node1, node2))
    
    def create_tree_topology(self):
        """Tree topology: hierarchical structure"""
        # Cloud at top
        cloud = NetworkNode(600, 150, "cloud", "CLOUD1")
        self.nodes.append(cloud)
        
        # Level 1: Routers
        router1 = NetworkNode(400, 300, "router", "ROUTER1")
        router2 = NetworkNode(800, 300, "router", "ROUTER2")
        self.nodes.extend([router1, router2])
        
        cloud.connections.extend([router1, router2])
        router1.connections.append(cloud)
        router2.connections.append(cloud)
        self.connections.extend([(cloud, router1), (cloud, router2)])
        
        # Level 2: Switches
        switches = []
        for i, x in enumerate([300, 500, 700, 900]):
            switch = NetworkNode(x, 450, "switch", f"SWITCH{i+1}")
            switches.append(switch)
            self.nodes.append(switch)
            
            parent = router1 if i < 2 else router2
            parent.connections.append(switch)
            switch.connections.append(parent)
            self.connections.append((parent, switch))
        
        # Level 3: PCs
        for i, switch in enumerate(switches):
            for j in range(2):
                pc = NetworkNode(switch.x - 50 + j*100, 600, "pc", f"PC{i*2+j+1}")
                self.nodes.append(pc)
                
                switch.connections.append(pc)
                pc.connections.append(switch)
                self.connections.append((switch, pc))
    
    def create_linear_topology(self):
        """Linear topology: nodes connected in a line"""
        num_nodes = 7
        start_x, y = 250, 400
        spacing = 150
        
        for i in range(num_nodes):
            x = start_x + i * spacing
            node = NetworkNode(x, y, "router", f"ROUTER{i+1}")
            self.nodes.append(node)
            
            if i > 0:
                prev_node = self.nodes[i-1]
                prev_node.connections.append(node)
                node.connections.append(prev_node)
                self.connections.append((prev_node, node))

    def build_random_topology(self):
        """Reset and build a fresh tree topology"""
        self.log_debug("=== BUILD TOPOLOGY CALLED ===")
        try:
            self.reset_network(confirm=False)
            # Ensure canvas metrics are ready
            self.canvas.update_idletasks()
            canvas_w = max(self.canvas.winfo_width(), 800)
            canvas_h = max(self.canvas.winfo_height(), 600)
            self.log_debug(f"Canvas size: {canvas_w} x {canvas_h}")

            self.generate_random_tree_topology(canvas_size=(canvas_w, canvas_h))
            node_count = len(self.nodes)
            self.log_debug(f"Nodes created: {node_count}")
            if node_count == 0:
                raise RuntimeError("Tree generation produced zero nodes.")

            if node_count:
                preview = [(node.name, round(node.x, 1), round(node.y, 1)) for node in self.nodes[:min(5, node_count)]]
                self.log_debug("Sample node coords (pre-scale):", preview)

            self.scale_topology_to_canvas()

            scaled_preview = [(node.name, round(node.x, 1), round(node.y, 1)) for node in self.nodes[:min(5, node_count)]]
            self.log_debug("Sample node coords (post-scale):", scaled_preview)

            self.draw_network()
            self.status_label.config(text="Generated random tree topology")
            self.populate_node_options()
            self.update_packet_details()
        except Exception as exc:
            self.log_debug("Topology generation failed:", exc)
            messagebox.showerror("Build Topology", f"Failed to build topology:\n{exc}")

    def generate_random_tree_topology(self, canvas_size=None):
        """Create a responsive multi-level tree that fits the canvas"""
        self.canvas.update_idletasks()
        if canvas_size:
            canvas_width = max(canvas_size[0], 800)
            canvas_height = max(canvas_size[1], 600)
        else:
            canvas_width = max(self.canvas.winfo_width(), 900)
            canvas_height = max(self.canvas.winfo_height(), 600)

        levels = random.randint(3, 4)
        nodes_per_level = [1]
        for lvl in range(1, levels):
            nodes_per_level.append(random.randint(2, min(5, 2 + lvl)))

        top_margin = 100
        horizontal_margin = 140
        usable_width = max(200, canvas_width - horizontal_margin * 2)
        level_spacing = (canvas_height - 2 * top_margin) / max(1, levels - 1)
        self.highlighted_path = []
        self.nodes.clear()
        self.connections.clear()

        previous_level_nodes = []
        for lvl, count in enumerate(nodes_per_level):
            y = top_margin + lvl * level_spacing
            level_nodes = []
            for idx in range(count):
                x_ratio = (idx + 1) / (count + 1)
                x = horizontal_margin + usable_width * x_ratio
                if lvl == 0:
                    node_type = "cloud"
                elif lvl == levels - 1:
                    node_type = "pc"
                else:
                    node_type = "router" if lvl == 1 else "switch"
                name = f"{node_type.upper()}{len([n for n in self.nodes if n.type == node_type]) + 1}"
                node = NetworkNode(x, y, node_type, name)
                self.nodes.append(node)
                level_nodes.append(node)

                if previous_level_nodes:
                    parent = previous_level_nodes[idx % len(previous_level_nodes)]
                    parent.connections.append(node)
                    node.connections.append(parent)
                    self.connections.append((parent, node))
            previous_level_nodes = level_nodes
        self.log_debug(f"Generated tree levels: {nodes_per_level}")
    
    def add_node(self, node_type):
        x = random.randint(100, 800)
        y = random.randint(100, 600)
        name = f"{node_type.upper()}{len([n for n in self.nodes if n.type == node_type]) + 1}"
        node = NetworkNode(x, y, node_type, name)
        self.nodes.append(node)
        self.draw_network()
        self.status_label.config(text=f"Added {name}")
        self.populate_node_options()
        
    def toggle_connection_mode(self):
        self.connection_mode = not self.connection_mode
        if self.connection_mode:
            self.conn_button.config(bg=self.colors['success'], text="✓ Connecting...")
            self.status_label.config(text="Click two nodes to connect them")
        else:
            self.conn_button.config(bg=self.colors['accent_secondary'], text="🔗 Connect Nodes")
            self.selected_node = None
            self.status_label.config(text="Ready")
        self.draw_network()
        
    def on_canvas_click(self, event):
        clicked_node = self.get_node_at(event.x, event.y)
        
        if self.connection_mode and clicked_node:
            if self.selected_node is None:
                self.selected_node = clicked_node
                self.status_label.config(text=f"Selected {clicked_node.name}, click another node")
            elif self.selected_node != clicked_node:
                if clicked_node not in self.selected_node.connections:
                    self.selected_node.connections.append(clicked_node)
                    clicked_node.connections.append(self.selected_node)
                    self.connections.append((self.selected_node, clicked_node))
                    self.status_label.config(text=f"Connected {self.selected_node.name} ↔ {clicked_node.name}")
                self.selected_node = None
            self.draw_network()
        elif clicked_node:
            self.dragging_node = clicked_node
            
    def on_canvas_drag(self, event):
        if self.dragging_node and not self.connection_mode:
            self.dragging_node.x = event.x
            self.dragging_node.y = event.y
            self.draw_network()
            
    def on_canvas_release(self, event):
        self.dragging_node = None
        
    def on_right_click(self, event):
        clicked_node = self.get_node_at(event.x, event.y)
        if clicked_node:
            self.show_node_info(clicked_node)
    
    # NEW: Handle canvas mouse motion for tooltips
    def on_canvas_motion(self, event):
        """Show tooltip when hovering over packet"""
        # Find packet at mouse position
        hovered_packet = None
        min_dist = 20  # Maximum distance to show tooltip
        
        for packet in self.packets:
            if packet.current_index < len(packet.path) - 1:
                node1 = packet.path[packet.current_index]
                node2 = packet.path[packet.current_index + 1]
                x = node1.x + (node2.x - node1.x) * packet.progress
                y = node1.y + (node2.y - node1.y) * packet.progress
                
                dist = math.sqrt((x - event.x)**2 + (y - event.y)**2)
                if dist < min_dist:
                    min_dist = dist
                    hovered_packet = (packet, x, y)
        
        # Show tooltip if packet found
        if hovered_packet:
            packet, x, y = hovered_packet
            self.show_packet_tooltip(packet, x, y)
        else:
            self.hide_tooltip()
    
    # NEW: Hide tooltip when leaving canvas
    def on_canvas_leave(self, event):
        self.hide_tooltip()
    
    # NEW: Show packet tooltip
    def show_packet_tooltip(self, packet, x, y):
        """Display tooltip with packet information"""
        if self.tooltip_window:
            self.tooltip_window.destroy()
        
        # Get absolute canvas position
        canvas_x = self.canvas.winfo_rootx()
        canvas_y = self.canvas.winfo_rooty()
        
        tooltip_x = canvas_x + x + 20
        tooltip_y = canvas_y + y - 20
        
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        
        if tooltip_x + 220 > screen_width:
            tooltip_x = canvas_x + x - 240
        if tooltip_y < 0:
            tooltip_y = canvas_y + y + 20
        if tooltip_y + 120 > screen_height:
            tooltip_y = screen_height - 140
        
        self.tooltip_window = tk.Toplevel(self.root)
        self.tooltip_window.overrideredirect(True)
        self.tooltip_window.configure(
            bg=self.colors['surface'],
            highlightbackground=self.colors['border'],
            highlightthickness=1
        )
        self.tooltip_window.geometry(f"+{int(tooltip_x)}+{int(tooltip_y)}")
        
        # Tooltip content
        hops_remaining = len(packet.path) - packet.current_index - 1
        tooltip_text = f"Packet ID: {packet.packet_id}\n"
        tooltip_text += f"cwnd: {packet.cwnd:.1f} MSS\n"
        tooltip_text += f"Phase: {packet.phase.replace('_', ' ').title()}\n"
        tooltip_text += f"RTT: {packet.rtt:.1f}ms\n"
        tooltip_text += f"Hops remaining: {hops_remaining}"
        
        label = tk.Label(
            self.tooltip_window,
            text=tooltip_text,
            bg=self.colors['surface'],
            fg=self.colors['text'],
            font=("Segoe UI", 9),
            justify=tk.LEFT
        )
        label.pack(padx=5, pady=5)
    
    # NEW: Hide tooltip
    def hide_tooltip(self):
        """Hide packet tooltip"""
        if self.tooltip_window:
            self.tooltip_window.destroy()
            self.tooltip_window = None
            
    def get_node_at(self, x, y):
        for node in self.nodes:
            dist = math.sqrt((node.x - x)**2 + (node.y - y)**2)
            if dist < 30:
                return node
        return None
        
    def draw_network(self):
        # Double-buffered, tag-based drawing
        # Prevent concurrent redraws
        if self.redraw_scheduled:
            return

        now = time.time()
        if now - self.last_draw_time < self.min_draw_interval:
            # schedule to try again later
            if self.simulation_running or self.manual_packet_mode:
                self.root.after(int(self.min_draw_interval * 1000), self.draw_network)
            return

        self.redraw_scheduled = True
        self.last_draw_time = now

        try:
            # delete only tagged objects to avoid full canvas clear flicker
            try:
                self.canvas.delete("connection")
                self.canvas.delete("packet")
                self.canvas.delete("node")
                self.canvas.delete("label")
                self.canvas.delete("bandwidth")
            except Exception:
                pass

            # ensure canvas geometry is available
            self.canvas.update_idletasks()
            canvas_width = max(self.canvas.winfo_width(), 100)
            canvas_height = max(self.canvas.winfo_height(), 100)
            if canvas_width <= 100 or canvas_height <= 100:
                return

            # draw layers
            self._draw_connections()
            self._draw_packets()
            self._draw_nodes()

        finally:
            self.redraw_scheduled = False

        if self.simulation_running or self.manual_packet_mode:
            self.root.after(int(self.min_draw_interval * 1000), self.draw_network)

            
    def toggle_simulation(self):
        self.simulation_running = not self.simulation_running
        self.manual_packet_mode = False  # Exit manual mode when toggling
        
        if self.simulation_running:
            self.sim_button.config(text="⏸ Pause", bg=self.colors['accent_dark'])
            self.status_label.config(text="Simulation running...")
            self.start_packet_generation()
            self.decay_congestion()
            self.update_status_bar()
            # Separate update loops
            self.update_bandwidth_labels()
            self.draw_network()
        else:
            self.sim_button.config(text="▶ Simulate", bg=self.colors['accent'])
            self.status_label.config(text="Paused")
            if self.status_update_timer:
                self.root.after_cancel(self.status_update_timer)
            self.stop_packet_details_updates()
            self.update_packet_details()

    # --- Drawing layer helpers ---
    def _draw_connections(self):
        for node1, node2 in self.connections:
            color = self.colors['text_muted'] if not self.simulation_running else self.colors['accent']
            width = 2
            if self.highlighted_path and len(self.highlighted_path) > 1:
                for i in range(len(self.highlighted_path) - 1):
                    if ((node1 == self.highlighted_path[i] and node2 == self.highlighted_path[i+1]) or
                        (node2 == self.highlighted_path[i] and node1 == self.highlighted_path[i+1])):
                        color = self.colors['warning']
                        width = 4
                        break

            self.canvas.create_line(node1.x, node1.y, node2.x, node2.y,
                                   fill=color, width=width, dash=(5, 3) if width == 2 else None,
                                   tags=("connection",))

            if self.simulation_running:
                max_bandwidth = 10
                current_utilization = min((node1.congestion + node2.congestion) / 2, max_bandwidth)
                utilization_percent = (current_utilization / max_bandwidth) * 100
                label_color = (self.colors['success'] if utilization_percent < 50 else
                               (self.colors['warning'] if utilization_percent < 80 else self.colors['error']))
                mid_x = (node1.x + node2.x) / 2
                mid_y = (node1.y + node2.y) / 2
                bandwidth_text = f"{current_utilization:.1f} / {max_bandwidth} Gbps"
                self.canvas.create_text(mid_x, mid_y - 10, text=bandwidth_text,
                                       font=("Segoe UI", 8), fill=label_color, tags=("bandwidth",))

    def _draw_packets(self):
        packets_to_remove = []
        # iterate on a copy
        for packet in list(self.packets):
            if packet.current_index >= len(packet.path) - 1:
                packet.completed = True
                self.record_packet_event(packet, "delivered")
                packets_to_remove.append(packet)
                continue

            node1 = packet.path[packet.current_index]
            node2 = packet.path[packet.current_index + 1]

            # handle congestion only at hop start
            if packet.progress == 0:
                self.handle_congestion_control(packet, node1)

            x = node1.x + (node2.x - node1.x) * packet.progress
            y = node1.y + (node2.y - node1.y) * packet.progress

            packet_size = max(5, min(15, int(5 + packet.cwnd * 0.5)))

            self.canvas.create_oval(x-packet_size, y-packet_size, x+packet_size, y+packet_size,
                                   fill=packet.color, outline=self.colors['bg_secondary'], width=2,
                                   tags=("packet", f"packet_{packet.packet_id}"))

            speed_factor = max(0.01, 0.05 * (1 - node1.congestion * 0.05))
            packet.progress += speed_factor
            if packet.progress >= 1.0:
                packet.progress = 0
                packet.current_index += 1
                self.record_packet_event(packet, "hop_completed")

        # remove delivered packets
        if packets_to_remove:
            self.packets = [p for p in self.packets if p not in packets_to_remove]

    def _draw_nodes(self):
        for node in self.nodes:
            color = self.colors.get(node.type, self.colors['accent'])

            if node == self.selected_node:
                self.canvas.create_oval(node.x-35, node.y-35, node.x+35, node.y+35,
                                       fill="", outline=self.colors['accent'], width=3, tags=("node",))

            self.canvas.create_oval(node.x-30, node.y-30, node.x+30, node.y+30,
                                   fill=color, outline="white", width=2, tags=("node",))

            icons = {'cloud': '☁', 'router': '⚡', 'switch': '⊞', 'pc': '💻'}
            self.canvas.create_text(node.x, node.y-5, text=icons.get(node.type, '?'),
                                   font=("Segoe UI", 20), fill=self.colors['text'], tags=("node",))

            self.canvas.create_text(node.x, node.y+45, text=node.name,
                                   font=("Segoe UI", 9, "bold"), fill=self.colors['text'], tags=("label",))

            if node.congestion > 0:
                congestion_level = node.get_congestion_level()
                cong_color = (self.colors['success'] if congestion_level == 'low' else
                              (self.colors['warning'] if congestion_level in ['medium', 'high'] else self.colors['error']))
                self.canvas.create_oval(node.x+20, node.y-20, node.x+30, node.y-10,
                                       fill=cong_color, outline="white", width=2, tags=("node",))
                self.canvas.create_text(node.x+25, node.y-15, text=str(int(node.congestion)),
                                       font=("Segoe UI", 7, "bold"), fill="white", tags=("node",))

    # --- Canvas / Topology helpers ---
    def get_canvas_bounds(self):
        try:
            self.canvas.update_idletasks()
        except Exception:
            pass
        width = max(self.canvas.winfo_width(), 400)
        height = max(self.canvas.winfo_height(), 300)
        return {
            'min_x': self.topology_margin,
            'max_x': width - self.topology_margin,
            'min_y': self.topology_margin,
            'max_y': height - self.topology_margin,
            'center_x': width / 2,
            'center_y': height / 2,
            'width': max(100, width - 2 * self.topology_margin),
            'height': max(100, height - 2 * self.topology_margin)
        }

    def scale_topology_to_canvas(self):
        if not self.nodes:
            return

        min_x = min(node.x for node in self.nodes)
        max_x = max(node.x for node in self.nodes)
        min_y = min(node.y for node in self.nodes)
        max_y = max(node.y for node in self.nodes)

        current_width = max_x - min_x if max_x > min_x else 1
        current_height = max_y - min_y if max_y > min_y else 1

        bounds = self.get_canvas_bounds()
        scale_x = bounds['width'] / current_width
        scale_y = bounds['height'] / current_height
        scale = min(scale_x, scale_y, 1.0)

        scaled_width = current_width * scale
        scaled_height = current_height * scale
        offset_x = bounds['center_x'] - (scaled_width / 2)
        offset_y = bounds['center_y'] - (scaled_height / 2)

        for node in self.nodes:
            node.x = ((node.x - min_x) * scale) + offset_x
            node.y = ((node.y - min_y) * scale) + offset_y
            # Clamp within bounds
            node.x = min(max(bounds['min_x'], node.x), bounds['max_x'])
            node.y = min(max(bounds['min_y'], node.y), bounds['max_y'])

        self.log_debug("Scaled topology to canvas bounds:", bounds)

    # --- Bandwidth / UI helpers ---
    def update_bandwidth_labels(self):
        if not self.simulation_running:
            return
        try:
            self.canvas.delete("bandwidth")
        except Exception:
            pass

        for node1, node2 in self.connections:
            max_bandwidth = 10
            current_utilization = min((node1.congestion + node2.congestion) / 2, max_bandwidth)
            utilization_percent = (current_utilization / max_bandwidth) * 100
            label_color = (self.colors['success'] if utilization_percent < 50 else
                           (self.colors['warning'] if utilization_percent < 80 else self.colors['error']))
            mid_x = (node1.x + node2.x) / 2
            mid_y = (node1.y + node2.y) / 2
            self.canvas.create_text(mid_x, mid_y - 10, text=f"{current_utilization:.1f} / {max_bandwidth} Gbps",
                                   font=("Segoe UI", 8), fill=label_color, tags=("bandwidth",))

        if self.simulation_running:
            self.root.after(500, self.update_bandwidth_labels)

    # --- Packet details update loop separate from canvas ---
    def schedule_packet_details_updates(self):
        if not self.manual_packet_mode:
            return
        # Update details for first active manual packet
        if self.active_manual_packet_ids:
            for packet in self.packets:
                if packet.packet_id in self.active_manual_packet_ids:
                    try:
                        self._show_manual_packet_details(packet)
                    except Exception:
                        pass
                    break

        if self.manual_packet_mode:
            self.root.after(150, self.schedule_packet_details_updates)

    def stop_packet_details_updates(self):
        self.manual_packet_mode = False
        try:
            for widget in self.packet_details_frame.winfo_children():
                widget.destroy()
            tk.Label(self.packet_details_frame, text="No active packets", bg=self.colors['surface'],
                     fg=self.colors['text_secondary'], font=("Segoe UI", 10, "italic")).pack(pady=30)
        except Exception:
            pass
    
    # NEW: Update status bar with algorithm and phase distribution
    def update_status_bar(self):
        """Update status bar with real-time algorithm and phase information"""
        if not self.simulation_running:
            return
        
        algo_name = "Reno" if self.congestion_algorithm == "reno" else "Tahoe"
        
        phase_counts = self.get_phase_counts()
        
        # Calculate loss rate
        if len(self.packets) > 0:
            lost_count = sum(1 for p in self.packets if p.lost)
            loss_rate = (lost_count / len(self.packets)) * 100
        else:
            loss_rate = 0
        
        # Format status text
        status_text = f"{algo_name} | Active: SS:{phase_counts['slow_start']}, "
        status_text += f"CA:{phase_counts['congestion_avoidance']}, "
        status_text += f"FR:{phase_counts['fast_retransmit']}, "
        status_text += f"FRec:{phase_counts['fast_recovery']} | Loss Rate: {loss_rate:.1f}%"
        
        self.status_label.config(text=status_text)
        
        # Schedule next update
        self.status_update_timer = self.root.after(1000, self.update_status_bar)
            
    def start_packet_generation(self):
        if self.simulation_running and len(self.nodes) > 1:
            # Enforce max packet limit in performance mode
            if len(self.packets) < self.max_packets:
                source = random.choice(self.nodes)
                destination = random.choice([n for n in self.nodes if n != source])
                self.spawn_packet(source, destination, manual=False)
            else:
                # Avoid spamming status too often
                try:
                    self.status_label.config(text=f"Packet limit ({self.max_packets}) reached - waiting for delivery")
                except Exception:
                    pass

            # Continue scheduling
            self.root.after(self.packet_generation_rate, self.start_packet_generation)

    # NEW: Generic packet creation helper (random + manual)
    def spawn_packet(self, source, destination, manual=False):
        """Create a packet between two nodes, respecting congestion settings"""
        path, total_latency = self.dijkstra_shortest_path(source, destination)
        if not path:
            if manual:
                messagebox.showwarning("No Path", "Selected nodes are not connected.")
            return False
        
        # Packet loss simulation (disabled for manual sends)
        next_packet_id = self.packet_counter + 1
        if not manual and random.random() < self.packet_loss_rate / 100.0:
            self.record_packet_event_dropped(next_packet_id)
            self.packet_counter = next_packet_id
            self.update_real_time_stats()
            return False
        
        self.packet_counter = next_packet_id
        packet = Packet(source, destination, path, packet_id=self.packet_counter)
        packet.total_latency = total_latency
        self.packets.append(packet)
        
        # Record packet creation event
        event_type = "manual_created" if manual else "created"
        self.record_packet_event(packet, event_type)
        
        # Update congestion based on traffic load
        congestion_factor = 1
        if self.traffic_load == "light":
            congestion_factor = 0.5
        elif self.traffic_load == "heavy":
            congestion_factor = 2
        
        for node in path:
            node.congestion = min(10, node.congestion + congestion_factor)
        
        # Track metrics + stats
        self.track_performance(total_latency, len(path))
        self.update_real_time_stats()
        return True

    # NEW: Manual packet trigger
    def send_manual_packet(self):
        """Send a user-selected packet and enter focused mode"""
        if len(self.nodes) < 2:
            messagebox.showwarning("No Nodes", "Create a topology first.")
            return
        
        source_name = self.manual_source_var.get()
        dest_name = self.manual_dest_var.get()
        
        if not source_name or not dest_name or source_name == dest_name:
            messagebox.showwarning("Invalid", "Select two different nodes.")
            return
        
        source_node = next((n for n in self.nodes if n.name == source_name), None)
        dest_node = next((n for n in self.nodes if n.name == dest_name), None)
        if not source_node or not dest_node:
            messagebox.showerror("Error", "Nodes not found.")
            return
        
        # Pause automatic simulation
        was_running = self.simulation_running
        if was_running:
            self.simulation_running = False
            self.sim_button.config(text="▶ Simulate")
        
        # Enter manual packet mode
        self.manual_packet_mode = True
        
        # Send the packet
        if self.spawn_packet(source_node, dest_node, manual=True):
            # Get the last added packet (the manual one)
            if self.packets:
                manual_packet = self.packets[-1]
                self.active_manual_packet_ids.add(manual_packet.packet_id)
                
                # Show detailed panel for this packet
                self._show_manual_packet_details(manual_packet)
                self.status_label.config(text=f"Manual Mode: {source_name} → {dest_name} (Press ▶ to resume auto)")
                self.schedule_packet_details_updates()
        else:
            self.manual_packet_mode = False
            if self.simulation_running:
                self.schedule_packet_details_updates()
            else:
                self.update_packet_details()
    
    def _show_manual_packet_details(self, packet):
        """Display detailed analysis for a manual packet"""
        # Clear and update packet details panel
        for widget in self.packet_details_frame.winfo_children():
            widget.destroy()
        
        # Title
        tk.Label(self.packet_details_frame, text=f"Packet #{packet.packet_id}", 
                font=("Segoe UI", 12, "bold"), bg=self.colors['surface'], 
                fg=self.colors['accent']).pack(anchor='w', padx=10, pady=10)
        
        # Route info
        route_text = f"{packet.source.name} → {packet.destination.name}"
        tk.Label(self.packet_details_frame, text=route_text, font=("Segoe UI", 10),
                bg=self.colors['surface'], fg=self.colors['text']).pack(anchor='w', padx=10)
        
        # Metrics container
        metrics_frame = tk.Frame(self.packet_details_frame, bg=self.colors['panel_bg'], relief=tk.RAISED, bd=1)
        metrics_frame.pack(fill=tk.X, padx=10, pady=10)
        
        # Create metric rows
        metrics = [
            ("Phase", lambda: packet.phase.replace('_', ' ').title(), packet.color),
            ("cwnd (MSS)", lambda: f"{packet.cwnd:.2f}", self.colors['accent']),
            ("RTT (ms)", lambda: f"{packet.rtt:.2f}", self.colors['warning']),
            ("Hops Total", lambda: str(len(packet.path) - 1), self.colors['success']),
            ("Hops Remaining", lambda: str(len(packet.path) - packet.current_index - 1), self.colors['text']),
            ("Progress", lambda: f"{min(100, int((packet.current_index + packet.progress) / len(packet.path) * 100))}%", self.colors['accent']),
            ("Status", lambda: "Delivered" if packet.completed else ("Lost" if packet.lost else "In Transit"), 
             self.colors['success'] if packet.completed else (self.colors['error'] if packet.lost else self.colors['warning'])),
        ]
        
        for label, value_fn, color in metrics:
            row = tk.Frame(metrics_frame, bg=self.colors['panel_bg'])
            row.pack(fill=tk.X, padx=8, pady=4)
            
            tk.Label(row, text=label + ":", bg=self.colors['panel_bg'], 
                    fg=self.colors['text_secondary'], font=("Segoe UI", 9)).pack(side=tk.LEFT)
            tk.Label(row, text=value_fn(), bg=self.colors['panel_bg'], 
                    fg=color, font=("Segoe UI", 10, "bold")).pack(side=tk.RIGHT)
        
        # Bandwidth & Throughput Section
        tk.Label(self.packet_details_frame, text="Network Analytics", 
                font=("Segoe UI", 11, "bold"), bg=self.colors['surface'], 
                fg=self.colors['accent']).pack(anchor='w', padx=10, pady=(15, 5))
        
        analytics_frame = tk.Frame(self.packet_details_frame, bg=self.colors['panel_bg'], relief=tk.RAISED, bd=1)
        analytics_frame.pack(fill=tk.X, padx=10, pady=5)
        
        # Current node bandwidth
        if packet.current_index < len(packet.path):
            current_node = packet.path[packet.current_index]
            next_node = packet.path[min(packet.current_index + 1, len(packet.path) - 1)]
            
            # Calculate throughput for this packet
            link_throughput = (packet.cwnd * 1500 * 8) / (max(packet.rtt, 1) / 1000) / 1000000  # Mbps
            
            row = tk.Frame(analytics_frame, bg=self.colors['panel_bg'])
            row.pack(fill=tk.X, padx=8, pady=4)
            tk.Label(row, text="Current Link:", bg=self.colors['panel_bg'], 
                    fg=self.colors['text_secondary'], font=("Segoe UI", 9)).pack(side=tk.LEFT)
            tk.Label(row, text=f"{current_node.name} → {next_node.name}", bg=self.colors['panel_bg'], 
                    fg=self.colors['accent'], font=("Segoe UI", 9, "bold")).pack(side=tk.RIGHT)
            
            row = tk.Frame(analytics_frame, bg=self.colors['panel_bg'])
            row.pack(fill=tk.X, padx=8, pady=4)
            tk.Label(row, text="Link Bandwidth:", bg=self.colors['panel_bg'], 
                    fg=self.colors['text_secondary'], font=("Segoe UI", 9)).pack(side=tk.LEFT)
            max_bw = 10  # Gbps
            utilization = min(100, int((link_throughput / (max_bw * 1000)) * 100))
            color = self.colors['success'] if utilization < 50 else (self.colors['warning'] if utilization < 80 else self.colors['error'])
            tk.Label(row, text=f"{link_throughput:.2f} Mbps / {max_bw*1000} Mbps ({utilization}%)", 
                    bg=self.colors['panel_bg'], fg=color, font=("Segoe UI", 9, "bold")).pack(side=tk.RIGHT)
            
            row = tk.Frame(analytics_frame, bg=self.colors['panel_bg'])
            row.pack(fill=tk.X, padx=8, pady=4)
            tk.Label(row, text="Link Latency:", bg=self.colors['panel_bg'], 
                    fg=self.colors['text_secondary'], font=("Segoe UI", 9)).pack(side=tk.LEFT)
            tk.Label(row, text=f"{current_node.latency}ms", bg=self.colors['panel_bg'], 
                    fg=self.colors['text'], font=("Segoe UI", 9, "bold")).pack(side=tk.RIGHT)
            
            row = tk.Frame(analytics_frame, bg=self.colors['panel_bg'])
            row.pack(fill=tk.X, padx=8, pady=4)
            tk.Label(row, text="Congestion Level:", bg=self.colors['panel_bg'], 
                    fg=self.colors['text_secondary'], font=("Segoe UI", 9)).pack(side=tk.LEFT)
            cong_level = current_node.get_congestion_level()
            cong_color = self.colors['success'] if cong_level == 'low' else (self.colors['warning'] if cong_level in ['medium', 'high'] else self.colors['error'])
            tk.Label(row, text=cong_level.upper(), bg=self.colors['panel_bg'], 
                    fg=cong_color, font=("Segoe UI", 9, "bold")).pack(side=tk.RIGHT)
        
        # Algorithm info
        tk.Label(self.packet_details_frame, text="Algorithm Details", 
                font=("Segoe UI", 11, "bold"), bg=self.colors['surface'], 
                fg=self.colors['accent']).pack(anchor='w', padx=10, pady=(15, 5))
        
        algo_frame = tk.Frame(self.packet_details_frame, bg=self.colors['panel_bg'], relief=tk.RAISED, bd=1)
        algo_frame.pack(fill=tk.X, padx=10, pady=5)
        
        algo_name = "TCP Reno" if self.congestion_algorithm == "reno" else "TCP Tahoe"
        row = tk.Frame(algo_frame, bg=self.colors['panel_bg'])
        row.pack(fill=tk.X, padx=8, pady=4)
        tk.Label(row, text="Algorithm:", bg=self.colors['panel_bg'], 
                fg=self.colors['text_secondary'], font=("Segoe UI", 9)).pack(side=tk.LEFT)
        tk.Label(row, text=algo_name, bg=self.colors['panel_bg'], 
                fg=self.colors['accent'], font=("Segoe UI", 9, "bold")).pack(side=tk.RIGHT)
        
        row = tk.Frame(algo_frame, bg=self.colors['panel_bg'])
        row.pack(fill=tk.X, padx=8, pady=4)
        tk.Label(row, text="ssthresh (MSS):", bg=self.colors['panel_bg'], 
                fg=self.colors['text_secondary'], font=("Segoe UI", 9)).pack(side=tk.LEFT)
        tk.Label(row, text=f"{packet.ssthresh:.2f}", bg=self.colors['panel_bg'], 
                fg=self.colors['text'], font=("Segoe UI", 9, "bold")).pack(side=tk.RIGHT)
        
        row = tk.Frame(algo_frame, bg=self.colors['panel_bg'])
        row.pack(fill=tk.X, padx=8, pady=4)
        tk.Label(row, text="Dup ACKs:", bg=self.colors['panel_bg'], 
                fg=self.colors['text_secondary'], font=("Segoe UI", 9)).pack(side=tk.LEFT)
        tk.Label(row, text=str(packet.dup_ack_count), bg=self.colors['panel_bg'], 
                fg=self.colors['text'], font=("Segoe UI", 9, "bold")).pack(side=tk.RIGHT)
        
        # Progress bar
        progress_pct = min(100, int((packet.current_index + packet.progress) / len(packet.path) * 100))
        
        tk.Label(self.packet_details_frame, text="Transmission Progress", 
                font=("Segoe UI", 10, "bold"), bg=self.colors['surface'], 
                fg=self.colors['text']).pack(anchor='w', padx=10, pady=(15, 8))
        
        progress_bg = tk.Canvas(self.packet_details_frame, height=20, width=300, bg=self.colors['panel_bg'], 
                               highlightthickness=0)
        progress_bg.pack(fill=tk.X, padx=10, pady=5)
        max_bar_width = 300
        progress_width = int(progress_pct / 100 * max_bar_width)
        progress_bg.create_rectangle(0, 0, progress_width, 20, fill=packet.color, outline="")
        progress_bg.create_text(max_bar_width / 2, 10, text=f"{progress_pct}%", fill=self.colors['text'], font=("Segoe UI", 9, "bold"))
    
    # NEW: Update detailed packet view in loop
    def update_manual_packet_display(self):
        """Continuously update manual packet details"""
        if self.manual_packet_mode and self.active_manual_packet_ids:
            for packet in self.packets:
                if packet.packet_id in self.active_manual_packet_ids:
                    self._show_manual_packet_details(packet)
                    break
            else:
                self.active_manual_packet_ids.clear()
        elif self.manual_packet_mode:
            # Manual packets finished
            for widget in self.packet_details_frame.winfo_children():
                widget.destroy()
            tk.Label(
                self.packet_details_frame,
                text="Manual packet completed ✓",
                bg=self.colors['surface'],
                fg=self.colors['success'],
                font=("Segoe UI", 11, "bold")
            ).pack(pady=30)
            self.active_manual_packet_ids.clear()
            self.manual_packet_mode = False
            if self.simulation_running:
                self.schedule_packet_details_updates()
            else:
                self.update_packet_details()
            return
        
        if self.manual_packet_mode:
            self.root.after(100, self.update_manual_packet_display)

    
    # NEW: Record dropped packet event
    def record_packet_event_dropped(self, packet_id):
        """Record event for dropped packet"""
        current_time = time.time() - self.performance_start_time
        event = {
            'time': current_time,
            'packet_id': packet_id,
            'cwnd': 0,
            'phase': "dropped",
            'rtt': 0,
            'event_type': "dropped",
            'throughput': 0,
            'node_congestion': 0
        }
        self.packet_events.append(event)
    # NEW: Track performance over time
    def track_performance(self, latency, hops):
        """Track latency and throughput metrics over time"""
        current_time = time.time() - self.performance_start_time
        self.time_stamps.append(current_time)
        self.latency_history.append(latency)
        
        # Calculate throughput (simplified: packets per second * avg packet size)
        # Assuming 1500 bytes per packet, throughput in Mbps
        if len(self.time_stamps) > 1:
            time_diff = self.time_stamps[-1] - self.time_stamps[-2]
            if time_diff > 0:
                throughput = (1500 * 8) / (time_diff * 1000000)  # Convert to Mbps
                self.throughput_history.append(throughput)
            else:
                self.throughput_history.append(self.throughput_history[-1] if self.throughput_history else 0)
        else:
            self.throughput_history.append(0)
            
         # NEW: Update routing statistics
        self.routing_stats['total_packets'] += 1
        hop_count = hops - 1  # Convert path length to hop count
        
        if hop_count < self.routing_stats['min_hops']:
            self.routing_stats['min_hops'] = hop_count
        if hop_count > self.routing_stats['max_hops']:
            self.routing_stats['max_hops'] = hop_count
        
        # Update average hop count
        total_hops = self.routing_stats['avg_hop_count'] * (self.routing_stats['total_packets'] - 1) + hop_count
        self.routing_stats['avg_hop_count'] = total_hops / self.routing_stats['total_packets']
        
        # Store path in history (keep last 100)
        self.routing_stats['path_history'].append({
            'hops': hop_count,
            'latency': latency,
            'time': time.time() - self.performance_start_time
        })
        
        if len(self.routing_stats['path_history']) > 100:
            self.routing_stats['path_history'].pop(0)

        # Keep only last 50 data points
        if len(self.time_stamps) > 50:
            self.time_stamps.pop(0)
            self.latency_history.pop(0)
            self.throughput_history.pop(0)


    # NEW: Decay congestion over time (natural decrease)
    def decay_congestion(self):
        """Gradually reduce congestion on all nodes"""
        if self.simulation_running:
            for node in self.nodes:
                if node.congestion > 0:
                    # Decay rate based on traffic load
                    decay_rate = 0.1 if self.traffic_load == "heavy" else 0.2
                    node.congestion = max(0, node.congestion - decay_rate)
            
            # Call again after 500ms
            self.root.after(500, self.decay_congestion)

    # NEW: Show Performance Graphs Window
    def show_performance_graphs(self):
        if not self.latency_history or len(self.latency_history) < 2:
            messagebox.showinfo("No Data", "Start the simulation to collect performance data")
            return
        
        graph_window = tk.Toplevel(self.root)
        graph_window.title("Network Performance Graphs")
        graph_window.geometry("1400x1000")
        graph_window.configure(bg=self.colors['bg'])
        
        # Title
        title = tk.Label(graph_window, text="📈 Network Performance Analysis", 
                        font=("Segoe UI", 16, "bold"),
                        bg=self.colors['bg'], fg=self.colors['text'])
        title.pack(pady=15)
        
       
        # Create matplotlib figure with 6 subplots (2x3 grid)
        fig = plt.figure(figsize=(13, 9))
        fig.patch.set_facecolor(self.colors['bg_secondary'])
        
        # Original 4 graphs
        ax1 = plt.subplot(2, 3, 1)
        ax2 = plt.subplot(2, 3, 2)
        ax3 = plt.subplot(2, 3, 3)
        ax4 = plt.subplot(2, 3, 4)
        # New graphs
        ax5 = plt.subplot(2, 3, 5)
        ax6 = plt.subplot(2, 3, 6)
        
        # Graph 1: Latency over Time
        ax1.plot(self.time_stamps, self.latency_history, color='#0066cc', linewidth=2, marker='o', markersize=4)
        ax1.set_xlabel('Time (seconds)', color=self.colors['text_secondary'], fontsize=11)
        ax1.set_ylabel('Latency (ms)', color=self.colors['text_secondary'], fontsize=11)
        ax1.set_title('Network Latency Over Time', color=self.colors['text'], fontsize=13, fontweight='bold')
        
        # Graph 2: Throughput over Time
        ax2.plot(self.time_stamps, self.throughput_history, color='#28a745', linewidth=2, marker='s', markersize=4)
        ax2.set_xlabel('Time (seconds)', color=self.colors['text_secondary'], fontsize=11)
        ax2.set_ylabel('Throughput (Mbps)', color=self.colors['text_secondary'], fontsize=11)
        ax2.set_title('Network Throughput Over Time', color=self.colors['text'], fontsize=13, fontweight='bold')
        
        # Graph 3: Hop Count Distribution
        hop_counts = [packet.hop_count for packet in self.packets if hasattr(packet, 'hop_count')]
        if not hop_counts:
            # Use path lengths from history
            hop_counts = list(range(1, min(len(self.nodes), 10)))
            hop_frequencies = [random.randint(1, 10) for _ in hop_counts]
        else:
            hop_frequencies = [hop_counts.count(i) for i in range(max(hop_counts) + 1)]
            hop_counts = list(range(max(hop_counts) + 1))
        
        ax3.bar(hop_counts, hop_frequencies, color='#6610f2', alpha=0.9, edgecolor=self.colors['surface'], linewidth=1)
        ax3.set_xlabel('Number of Hops', color=self.colors['text_secondary'], fontsize=11)
        ax3.set_ylabel('Frequency', color=self.colors['text_secondary'], fontsize=11)
        ax3.set_title('Hop Count Distribution', color=self.colors['text'], fontsize=13, fontweight='bold')
        ax3.grid(True, alpha=0.3, color=self.colors['border'], axis='y')
        
        # NEW: Graph 4: Congestion Heatmap
        congestion_data = [node.congestion for node in self.nodes]
        node_names = [node.name for node in self.nodes]
        
        colors_map = [
            self.colors['success'] if c <= 1 else
            self.colors['warning'] if c <= 3 else
            self.colors['phase_fast_recovery'] if c <= 5 else
            self.colors['error']
            for c in congestion_data
        ]
        
        ax4.barh(node_names[:10], congestion_data[:10], color=colors_map[:10], alpha=0.85, edgecolor=self.colors['surface'])
        ax4.set_xlabel('Congestion Level', color=self.colors['text_secondary'], fontsize=11)
        ax4.set_ylabel('Node', color=self.colors['text_secondary'], fontsize=11)
        ax4.set_title('Node Congestion Levels', color=self.colors['text'], fontsize=13, fontweight='bold')
        ax4.grid(True, alpha=0.3, color=self.colors['border'], axis='x')
        
        # NEW: Graph 5: Congestion Window Evolution
        if self.packet_events:
            # Get multiple packets for overlay
            unique_packet_ids = list(set([e.get('packet_id') for e in self.packet_events if 'packet_id' in e]))[:5]  # Limit to 5 packets
            
            for pid in unique_packet_ids:
                packet_evts = [e for e in self.packet_events if e.get('packet_id') == pid]
                if packet_evts:
                    times = [e.get('time', 0) for e in packet_evts]
                    cwnds = [e.get('cwnd', 0) for e in packet_evts]
                    if times and cwnds:
                        ax5.plot(times, cwnds, linewidth=2, alpha=0.7, label=f'Packet {pid}')
            
            # Mark phase transitions
            for pid in unique_packet_ids[:1]:  # Mark transitions for first packet
                packet_evts = [e for e in self.packet_events if e.get('packet_id') == pid]
                if len(packet_evts) > 1:
                    prev_phase = packet_evts[0].get('phase', '')
                    for i, evt in enumerate(packet_evts[1:], 1):
                        current_phase = evt.get('phase', '')
                        if current_phase != prev_phase:
                            ax5.axvline(x=evt.get('time', 0), color='#fbbf24', linestyle='--', 
                                       linewidth=1, alpha=0.5)
                        prev_phase = current_phase
        
        ax5.set_xlabel('Time (seconds)', color=self.colors['text_secondary'], fontsize=11)
        ax5.set_ylabel('cwnd (MSS)', color=self.colors['text_secondary'], fontsize=11)
        ax5.set_title('Congestion Window Evolution', color=self.colors['text'], fontsize=13, fontweight='bold')
        legend5 = ax5.legend(loc='upper left', fontsize=8)
        if legend5:
            legend5.get_frame().set_facecolor(self.colors['surface'])
            legend5.get_frame().set_edgecolor(self.colors['border'])
            for text in legend5.get_texts():
                text.set_color(self.colors['text'])
        
        # NEW: Graph 6: Algorithm Comparison (if data available)
        # This would show comparison if user switched algorithms
        # For now, show current algorithm performance metrics
        algo_name = "Reno" if self.congestion_algorithm == "reno" else "Tahoe"
        
        # Calculate metrics
        if self.packet_events:
            cwnds = [e.get('cwnd', 0) for e in self.packet_events if 'cwnd' in e]
            throughputs = [e.get('throughput', 0) for e in self.packet_events if 'throughput' in e]
            avg_cwnd = sum(cwnds) / len(cwnds) if cwnds else 0
            max_cwnd = max(cwnds) if cwnds else 0
            avg_throughput = sum(throughputs) / len(throughputs) if throughputs else 0
            loss_count = sum(1 for e in self.packet_events if e.get('event_type') == 'dropped')
            loss_rate = (loss_count / len(self.packet_events)) * 100 if self.packet_events else 0
        else:
            avg_cwnd = 0
            max_cwnd = 0
            avg_throughput = 0
            loss_rate = 0
        
        metrics = ['Avg cwnd', 'Max cwnd', 'Avg Throughput\n(Mbps)', 'Loss Rate\n(%)']
        values = [avg_cwnd, max_cwnd, avg_throughput, loss_rate]
        colors_bar = ['#3b82f6', '#8b5cf6', '#10b981', '#ef4444']
        
        bars = ax6.bar(metrics, values, color=colors_bar, alpha=0.85, edgecolor=self.colors['surface'], linewidth=1)
        ax6.set_ylabel('Value', color=self.colors['text_secondary'], fontsize=11)
        ax6.set_title(f'Algorithm Performance: {algo_name}', color=self.colors['text'], fontsize=13, fontweight='bold')
        ax6.grid(True, alpha=0.3, color=self.colors['border'], axis='y')
        
        # Add value labels on bars
        for bar, val in zip(bars, values):
            height = bar.get_height()
            ax6.text(bar.get_x() + bar.get_width()/2., height,
                    f'{val:.1f}', ha='center', va='bottom', color=self.colors['text'], fontsize=9)

        self._style_axes([ax1, ax2, ax3, ax4, ax5, ax6])

        fig.subplots_adjust(hspace=0.35, wspace=0.28, left=0.06, right=0.98, top=0.93, bottom=0.08)
        
        # Embed matplotlib figure in tkinter window
        canvas_frame = tk.Frame(graph_window, bg=self.colors['bg'])
        canvas_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        canvas = FigureCanvasTkAgg(fig, master=canvas_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # Statistics Frame
        stats_frame = tk.Frame(graph_window, bg=self.colors['panel_bg'])
        stats_frame.pack(fill=tk.X, padx=20, pady=10)
        
        # Calculate statistics
        avg_latency = sum(self.latency_history) / len(self.latency_history)
        max_latency = max(self.latency_history)
        min_latency = min(self.latency_history)
        avg_throughput = sum(self.throughput_history) / len(self.throughput_history) if self.throughput_history else 0
        
        stats_text = f"📊 Statistics: Avg Latency: {avg_latency:.2f}ms | Min: {min_latency:.2f}ms | Max: {max_latency:.2f}ms | Avg Throughput: {avg_throughput:.2f}Mbps"
        
        stats_label = tk.Label(stats_frame, text=stats_text,
                              bg=self.colors['panel_bg'], fg=self.colors['text'],
                              font=("Segoe UI", 10, "bold"))
        stats_label.pack(pady=10)
        
        # Buttons
        btn_frame = tk.Frame(graph_window, bg=self.colors['bg'])
        btn_frame.pack(pady=10)
        
        def refresh_graphs():
            graph_window.destroy()
            self.show_performance_graphs()
        
        def export_data():
            import csv
            from datetime import datetime
            if not self.time_stamps:
                messagebox.showinfo("No Data", "No performance data to export yet.")
                return
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"network_performance_{timestamp}.csv"
            try:
                with open(filename, 'w', newline='') as csvfile:
                    writer = csv.writer(csvfile)
                    writer.writerow(['Time (s)', 'Latency (ms)', 'Throughput (Mbps)'])
                    for i in range(len(self.time_stamps)):
                        latency = self.latency_history[i] if i < len(self.latency_history) else 0
                        throughput = self.throughput_history[i] if i < len(self.throughput_history) else 0
                        writer.writerow([f"{self.time_stamps[i]:.2f}", f"{latency:.2f}", f"{throughput:.2f}"])
                messagebox.showinfo("Export Complete", f"Performance data exported to:\n{filename}")
            except Exception as exc:
                messagebox.showerror("Export Failed", f"Unable to export data:\n{exc}")
        
        self.create_button(btn_frame, "🔄 Refresh", refresh_graphs, self.colors['accent']).pack(side=tk.LEFT, padx=5)
        self.create_button(btn_frame, "💾 Export Data", export_data, self.colors['success']).pack(side=tk.LEFT, padx=5)


    # NEW: Show Routing Analysis Window
    def show_routing_analysis(self):
        if not self.nodes:
            messagebox.showwarning("No Network", "Create a network topology first")
            return
        
        if self.routing_stats['total_packets'] == 0:
            messagebox.showinfo("No Data", "Start simulation to collect routing data")
            return
        
        routing_window = tk.Toplevel(self.root)
        routing_window.title("Routing Analysis & Hop Count Statistics")
        routing_window.geometry("900x700")
        routing_window.configure(bg=self.colors['bg'])
        
        # Title
        title = tk.Label(routing_window, text="🧭 Routing Analysis Dashboard", 
                        font=("Segoe UI", 16, "bold"),
                        bg=self.colors['bg'], fg=self.colors['text'])
        title.pack(pady=15)
        
        # Create notebook for tabs
        notebook = ttk.Notebook(routing_window)
        notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Tab 1: Statistics Overview
        stats_frame = tk.Frame(notebook, bg=self.colors['canvas_bg'])
        notebook.add(stats_frame, text="📊 Statistics")
        
        stats_text = tk.Text(stats_frame, bg=self.colors['canvas_bg'], 
                            fg=self.colors['text'], font=("Consolas", 11),
                            wrap=tk.WORD)
        stats_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Calculate routing statistics
        stats_text.insert(tk.END, "=" * 60 + "\n")
        stats_text.insert(tk.END, "         ROUTING PERFORMANCE STATISTICS\n")
        stats_text.insert(tk.END, "=" * 60 + "\n\n")
        
        stats_text.insert(tk.END, f"Total Packets Routed: {self.routing_stats['total_packets']}\n")
        stats_text.insert(tk.END, f"Average Hop Count: {self.routing_stats['avg_hop_count']:.2f}\n")
        stats_text.insert(tk.END, f"Minimum Hops: {self.routing_stats['min_hops']}\n")
        stats_text.insert(tk.END, f"Maximum Hops: {self.routing_stats['max_hops']}\n\n")
        
        stats_text.insert(tk.END, "=" * 60 + "\n")
        stats_text.insert(tk.END, "         NETWORK TOPOLOGY ANALYSIS\n")
        stats_text.insert(tk.END, "=" * 60 + "\n\n")
        
        stats_text.insert(tk.END, f"Total Nodes: {len(self.nodes)}\n")
        stats_text.insert(tk.END, f"Total Links: {len(self.connections)}\n")
        if len(self.nodes) > 1:
            density = (2 * len(self.connections)) / (len(self.nodes) * (len(self.nodes) - 1)) * 100
        else:
            density = 0
        stats_text.insert(tk.END, f"Network Density: {density:.2f}%\n\n")
        
        # Node-wise routing statistics
        stats_text.insert(tk.END, "=" * 60 + "\n")
        stats_text.insert(tk.END, "         NODE ROUTING STATISTICS\n")
        stats_text.insert(tk.END, "=" * 60 + "\n\n")
        
        stats_text.insert(tk.END, f"{'Node':<15} {'Type':<10} {'Connections':<12} {'Traffic':<10}\n")
        stats_text.insert(tk.END, "-" * 60 + "\n")
        
        for node in sorted(self.nodes, key=lambda n: len(n.connections), reverse=True):
            traffic_level = "🔴 High" if node.congestion > 5 else "🟡 Med" if node.congestion > 2 else "🟢 Low"
            stats_text.insert(tk.END, f"{node.name:<15} {node.type:<10} {len(node.connections):<12} {traffic_level:<10}\n")
        
        stats_text.insert(tk.END, "\n" + "=" * 60 + "\n")
        stats_text.insert(tk.END, "         PATH EFFICIENCY ANALYSIS\n")
        stats_text.insert(tk.END, "=" * 60 + "\n\n")
        
        if self.routing_stats['path_history']:
            recent_paths = self.routing_stats['path_history'][-20:]
            avg_recent_hops = sum(p['hops'] for p in recent_paths) / len(recent_paths)
            avg_recent_latency = sum(p['latency'] for p in recent_paths) / len(recent_paths)
            
            stats_text.insert(tk.END, f"Recent Packets (Last 20):\n")
            stats_text.insert(tk.END, f"  Average Hops: {avg_recent_hops:.2f}\n")
            stats_text.insert(tk.END, f"  Average Latency: {avg_recent_latency:.2f}ms\n\n")
            
            # Efficiency score (lower is better)
            efficiency = (avg_recent_hops / self.routing_stats['avg_hop_count']) * 100 if self.routing_stats['avg_hop_count'] > 0 else 100
            stats_text.insert(tk.END, f"Routing Efficiency: {efficiency:.1f}%\n")
            
            if efficiency < 90:
                stats_text.insert(tk.END, "  ⚠️  Routing paths are longer than average\n")
            elif efficiency > 110:
                stats_text.insert(tk.END, "  ✅ Routing paths are shorter than average\n")
            else:
                stats_text.insert(tk.END, "  ℹ️  Routing paths are near average\n")
        
        stats_text.config(state=tk.DISABLED)
        
        # Tab 2: Hop Count Visualization
        viz_frame = tk.Frame(notebook, bg=self.colors['bg'])
        notebook.add(viz_frame, text="📈 Visualizations")
        
        # Create hop count distribution graph
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10, 5))
        fig.patch.set_facecolor(self.colors['bg_secondary'])
        
        # Graph 1: Hop Count Distribution
        if self.routing_stats['path_history']:
            hop_counts = [p['hops'] for p in self.routing_stats['path_history']]
            hop_range = range(int(min(hop_counts)), int(max(hop_counts)) + 1)
            hop_freq = [hop_counts.count(h) for h in hop_range]
            
            ax1.bar(hop_range, hop_freq, color='#6610f2', alpha=0.85, edgecolor=self.colors['surface'], linewidth=1)
            ax1.set_xlabel('Hop Count', color=self.colors['text_secondary'], fontsize=11)
            ax1.set_ylabel('Frequency', color=self.colors['text_secondary'], fontsize=11)
            ax1.set_title('Hop Count Distribution', color=self.colors['text'], fontsize=12, fontweight='bold')
        
        # Graph 2: Hop Count vs Latency
        if self.routing_stats['path_history']:
            hops_list = [p['hops'] for p in self.routing_stats['path_history']]
            latency_list = [p['latency'] for p in self.routing_stats['path_history']]
            
            ax2.scatter(hops_list, latency_list, color=self.colors['accent'], alpha=0.7, s=50, edgecolors=self.colors['surface'])
            ax2.set_xlabel('Hop Count', color=self.colors['text_secondary'], fontsize=11)
            ax2.set_ylabel('Latency (ms)', color=self.colors['text_secondary'], fontsize=11)
            ax2.set_title('Hop Count vs Latency Correlation', color=self.colors['text'], fontsize=12, fontweight='bold')

        self._style_axes([ax1, ax2])
        
        plt.tight_layout()
        
        # Embed matplotlib figure
        canvas_frame = tk.Frame(viz_frame, bg=self.colors['bg'])
        canvas_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        canvas = FigureCanvasTkAgg(fig, master=canvas_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # Tab 3: Path Comparison
        compare_frame = tk.Frame(notebook, bg=self.colors['canvas_bg'])
        notebook.add(compare_frame, text="🔍 Path Finder")
        
        # Add path comparison tool
        compare_label = tk.Label(compare_frame, text="Compare Routes Between Nodes", 
                                font=("Segoe UI", 13, "bold"),
                                bg=self.colors['canvas_bg'], fg=self.colors['text'])
        compare_label.pack(pady=15)
        
        select_frame = tk.Frame(compare_frame, bg=self.colors['panel_bg'])
        select_frame.pack(pady=10, padx=20, fill=tk.X)
        
        tk.Label(select_frame, text="Node A:", 
                bg=self.colors['panel_bg'], fg=self.colors['text'],
                font=("Segoe UI", 10)).grid(row=0, column=0, padx=10, pady=10)
        
        nodeA_var = tk.StringVar()
        nodeA_dropdown = ttk.Combobox(select_frame, textvariable=nodeA_var, 
                                     values=[node.name for node in self.nodes],
                                     state='readonly', width=15)
        nodeA_dropdown.grid(row=0, column=1, padx=10, pady=10)
        
        tk.Label(select_frame, text="Node B:", 
                bg=self.colors['panel_bg'], fg=self.colors['text'],
                font=("Segoe UI", 10)).grid(row=0, column=2, padx=10, pady=10)
        
        nodeB_var = tk.StringVar()
        nodeB_dropdown = ttk.Combobox(select_frame, textvariable=nodeB_var,
                                     values=[node.name for node in self.nodes],
                                     state='readonly', width=15)
        nodeB_dropdown.grid(row=0, column=3, padx=10, pady=10)
        
        compare_text = tk.Text(compare_frame, bg=self.colors['canvas_bg'], 
                              fg=self.colors['text'], font=("Consolas", 10),
                              wrap=tk.WORD, height=20)
        compare_text.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        def compare_routes():
            nodeA_name = nodeA_var.get()
            nodeB_name = nodeB_var.get()
            
            if not nodeA_name or not nodeB_name:
                messagebox.showwarning("Selection Required", "Please select both nodes")
                return
            
            nodeA = next((n for n in self.nodes if n.name == nodeA_name), None)
            nodeB = next((n for n in self.nodes if n.name == nodeB_name), None)
            
            if not nodeA or not nodeB or nodeA == nodeB:
                messagebox.showwarning("Invalid Selection", "Please select two different nodes")
                return
            
            path, latency = self.dijkstra_shortest_path(nodeA, nodeB)
            
            compare_text.config(state=tk.NORMAL)
            compare_text.delete(1.0, tk.END)
            
            if path:
                compare_text.insert(tk.END, "=" * 55 + "\n")
                compare_text.insert(tk.END, f"  ROUTE ANALYSIS: {nodeA.name} → {nodeB.name}\n")
                compare_text.insert(tk.END, "=" * 55 + "\n\n")
                
                compare_text.insert(tk.END, f"Total Hops: {len(path) - 1}\n")
                compare_text.insert(tk.END, f"Total Latency: {latency:.2f}ms\n")
                compare_text.insert(tk.END, f"Average Latency per Hop: {latency / (len(path) - 1):.2f}ms\n\n")
                
                compare_text.insert(tk.END, "Detailed Path:\n")
                compare_text.insert(tk.END, "-" * 55 + "\n")
                
                for i, node in enumerate(path):
                    compare_text.insert(tk.END, f"Hop {i}: {node.name} ({node.type})\n")
                    compare_text.insert(tk.END, f"  Latency: {node.latency}ms\n")
                    compare_text.insert(tk.END, f"  Congestion: {node.congestion:.1f}\n")
                    if i < len(path) - 1:
                        compare_text.insert(tk.END, "  ↓\n")
                
                compare_text.insert(tk.END, "\n" + "=" * 55 + "\n")
                
                # Comparison with network average
                if self.routing_stats['avg_hop_count'] > 0:
                    compare_text.insert(tk.END, "\nComparison with Network Average:\n")
                    compare_text.insert(tk.END, f"Network Avg Hops: {self.routing_stats['avg_hop_count']:.2f}\n")
                    compare_text.insert(tk.END, f"This Route Hops: {len(path) - 1}\n")
                    
                    if len(path) - 1 < self.routing_stats['avg_hop_count']:
                        compare_text.insert(tk.END, "✅ This route is shorter than average!\n")
                    elif len(path) - 1 > self.routing_stats['avg_hop_count']:
                        compare_text.insert(tk.END, "⚠️  This route is longer than average.\n")
                    else:
                        compare_text.insert(tk.END, "ℹ️  This route matches the network average.\n")
            else:
                compare_text.insert(tk.END, "❌ No route found between these nodes.\n")
            
            compare_text.config(state=tk.DISABLED)
        
        self.create_button(compare_frame, "🔍 Analyze Route", compare_routes, self.colors['accent']).pack(pady=10)
            
    def find_path(self, source, destination):
        # BFS to find path
        visited = set()
        queue = [(source, [source])]
        
        while queue:
            node, path = queue.pop(0)
            if node == destination:
                return path
                
            if node not in visited:
                visited.add(node)
                for neighbor in node.connections:
                    if neighbor not in visited:
                        queue.append((neighbor, path + [neighbor]))
        
        return None
    
    # NEW: Dijkstra's Shortest Path Algorithm
    def dijkstra_shortest_path(self, source, destination):
        """Find shortest path using Dijkstra's algorithm based on latency"""
        distances = {node: float('infinity') for node in self.nodes}
        distances[source] = 0
        previous = {node: None for node in self.nodes}
        unvisited = set(self.nodes)
        
        while unvisited:
            # Find node with minimum distance
            current = min(unvisited, key=lambda node: distances[node])
            
            if distances[current] == float('infinity'):
                break
            
            if current == destination:
                # Reconstruct path
                path = []
                while current:
                    path.append(current)
                    current = previous[current]
                return path[::-1], distances[destination]
            
            unvisited.remove(current)
            
            # Update distances to neighbors
            for neighbor in current.connections:
                if neighbor in unvisited:
                    # Calculate distance (using latency as weight)
                    alt_distance = distances[current] + current.latency
                    
                    if alt_distance < distances[neighbor]:
                        distances[neighbor] = alt_distance
                        previous[neighbor] = current
        
        return None, float('infinity')
    
    # NEW: Show Path Finder Window
    def show_path_finder(self):
        if len(self.nodes) < 2:
            messagebox.showwarning("Not Enough Nodes", "Add at least 2 nodes to find a path")
            return
        
        path_window = tk.Toplevel(self.root)
        path_window.title("Shortest Path Finder")
        path_window.geometry("500x600")
        path_window.configure(bg=self.colors['bg'])
        
        # Title
        title = tk.Label(path_window, text="🗺️ Dijkstra's Shortest Path", 
                        font=("Segoe UI", 16, "bold"),
                        bg=self.colors['bg'], fg=self.colors['text'])
        title.pack(pady=20)
        
        # Selection Frame
        select_frame = tk.Frame(path_window, bg=self.colors['panel_bg'])
        select_frame.pack(pady=10, padx=20, fill=tk.X)
        
        # Source selection
        tk.Label(select_frame, text="Source Node:", 
                bg=self.colors['panel_bg'], fg=self.colors['text'],
                font=("Segoe UI", 11)).grid(row=0, column=0, padx=10, pady=10, sticky='w')
        
        source_var = tk.StringVar()
        source_dropdown = ttk.Combobox(select_frame, textvariable=source_var, 
                                      values=[node.name for node in self.nodes],
                                      state='readonly', width=20)
        source_dropdown.grid(row=0, column=1, padx=10, pady=10)
        if self.nodes:
            source_dropdown.current(0)
        
        # Destination selection
        tk.Label(select_frame, text="Destination Node:", 
                bg=self.colors['panel_bg'], fg=self.colors['text'],
                font=("Segoe UI", 11)).grid(row=1, column=0, padx=10, pady=10, sticky='w')
        
        dest_var = tk.StringVar()
        dest_dropdown = ttk.Combobox(select_frame, textvariable=dest_var,
                                     values=[node.name for node in self.nodes],
                                     state='readonly', width=20)
        dest_dropdown.grid(row=1, column=1, padx=10, pady=10)
        if len(self.nodes) > 1:
            dest_dropdown.current(1)
        
        # Result display
        result_frame = tk.Frame(path_window, bg=self.colors['canvas_bg'])
        result_frame.pack(pady=20, padx=20, fill=tk.BOTH, expand=True)
        
        result_text = tk.Text(result_frame, bg=self.colors['canvas_bg'], 
                             fg=self.colors['text'], font=("Consolas", 10),
                             wrap=tk.WORD, height=15)
        result_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        def calculate_path():
            source_name = source_var.get()
            dest_name = dest_var.get()
            
            if not source_name or not dest_name:
                messagebox.showwarning("Selection Required", "Please select both source and destination")
                return
            
            if source_name == dest_name:
                messagebox.showwarning("Same Node", "Source and destination must be different")
                return
            
            # Find nodes
            source_node = next((n for n in self.nodes if n.name == source_name), None)
            dest_node = next((n for n in self.nodes if n.name == dest_name), None)
            
            if not source_node or not dest_node:
                messagebox.showerror("Error", "Could not find selected nodes")
                return
            
            # Calculate shortest path
            path, total_latency = self.dijkstra_shortest_path(source_node, dest_node)
            
            result_text.config(state=tk.NORMAL)
            result_text.delete(1.0, tk.END)
            
            if path:
                result_text.insert(tk.END, "=" * 50 + "\n")
                result_text.insert(tk.END, "SHORTEST PATH FOUND\n")
                result_text.insert(tk.END, "=" * 50 + "\n\n")
                
                result_text.insert(tk.END, f"Source: {source_node.name}\n")
                result_text.insert(tk.END, f"Destination: {dest_node.name}\n\n")
                
                result_text.insert(tk.END, f"Total Hops: {len(path) - 1}\n")
                result_text.insert(tk.END, f"Total Latency: {total_latency:.2f}ms\n\n")
                
                result_text.insert(tk.END, "Path Traversal:\n")
                result_text.insert(tk.END, "-" * 50 + "\n")
                
                for i, node in enumerate(path):
                    result_text.insert(tk.END, f"{i+1}. {node.name} ({node.type})")
                    if i < len(path) - 1:
                        result_text.insert(tk.END, f" → [Latency: {node.latency}ms]\n")
                    else:
                        result_text.insert(tk.END, "\n")
                
                result_text.insert(tk.END, "\n" + "=" * 50 + "\n")
                
                # Highlight path on canvas
                self.highlighted_path = path
                self.draw_network()
                
                messagebox.showinfo("Success", f"Path found with {len(path)-1} hops!")
            else:
                result_text.insert(tk.END, "=" * 50 + "\n")
                result_text.insert(tk.END, "NO PATH FOUND\n")
                result_text.insert(tk.END, "=" * 50 + "\n\n")
                result_text.insert(tk.END, f"No connection exists between\n")
                result_text.insert(tk.END, f"{source_node.name} and {dest_node.name}\n\n")
                result_text.insert(tk.END, "The nodes are not connected in the\n")
                result_text.insert(tk.END, "current network topology.\n")
                
                self.highlighted_path = []
                self.draw_network()
            
            result_text.config(state=tk.DISABLED)
        
        def clear_highlight():
            self.highlighted_path = []
            self.draw_network()
            result_text.config(state=tk.NORMAL)
            result_text.delete(1.0, tk.END)
            result_text.config(state=tk.DISABLED)
        
        # Buttons
        btn_frame = tk.Frame(path_window, bg=self.colors['bg'])
        btn_frame.pack(pady=10)
        
        self.create_button(btn_frame, "🔍 Find Shortest Path", calculate_path, self.colors['success']).pack(side=tk.LEFT, padx=5)
        self.create_button(btn_frame, "🗑️ Clear Highlight", clear_highlight, self.colors['warning']).pack(side=tk.LEFT, padx=5)
        
    # NEW: Show Packet Timeline Window
    def show_packet_timeline(self):
        """Display packet timeline analysis window with 4 graphs"""
        if not self.packet_events:
            messagebox.showinfo("No Data", "Start the simulation to collect packet timeline data")
            return
        
        timeline_window = tk.Toplevel(self.root)
        timeline_window.title("📦 Packet Timeline Analysis")
        timeline_window.geometry("1400x900")
        timeline_window.configure(bg=self.colors['bg'])
        
        # Title
        title = tk.Label(timeline_window, text="📦 Packet Timeline Analysis", 
                        font=("Segoe UI", 16, "bold"),
                        bg=self.colors['bg'], fg=self.colors['text'])
        title.pack(pady=15)
        
        # Create matplotlib figure with 4 subplots
        fig = plt.figure(figsize=(12, 8.5))
        fig.patch.set_facecolor(self.colors['bg_secondary'])
        
        # Get unique packet IDs for selection
        unique_packet_ids = list(set([e['packet_id'] for e in self.packet_events if 'packet_id' in e]))
        if not unique_packet_ids:
            messagebox.showinfo("No Data", "No packet events recorded yet")
            timeline_window.destroy()
            return
        
        # Select first packet for visualization
        selected_packet_id = unique_packet_ids[0] if unique_packet_ids else None
        packet_events = [e for e in self.packet_events if e.get('packet_id') == selected_packet_id]
        
        # Graph 1: Congestion Window Over Time
        ax1 = plt.subplot(2, 2, 1)
        if packet_events:
            times = [e.get('time', 0) for e in packet_events]
            cwnds = [e.get('cwnd', 0) for e in packet_events]
            phases = [e.get('phase', 'slow_start') for e in packet_events]
            
            # Color code by phase
            phase_colors = {
                "slow_start": self.colors['phase_slow_start'],
                "congestion_avoidance": self.colors['phase_congestion_avoid'],
                "fast_retransmit": self.colors['phase_fast_retransmit'],
                "fast_recovery": self.colors['phase_fast_recovery'],
                "dropped": self.colors['error']
            }
            
            # Plot segments by phase
            current_phase = None
            phase_start_idx = 0
            for i, phase in enumerate(phases):
                if phase != current_phase:
                    if current_phase is not None:
                        ax1.plot(times[phase_start_idx:i], cwnds[phase_start_idx:i],
                                color=phase_colors.get(current_phase, "#ffffff"),
                                linewidth=2, label=current_phase.replace("_", " ").title())
                    current_phase = phase
                    phase_start_idx = i
            # Plot last segment
            if current_phase:
                ax1.plot(times[phase_start_idx:], cwnds[phase_start_idx:],
                        color=phase_colors.get(current_phase, "#ffffff"),
                        linewidth=2, label=current_phase.replace("_", " ").title())
            
            # Mark packet loss events
            loss_events = [i for i, e in enumerate(packet_events) if e.get('event_type') == 'dropped']
            for idx in loss_events:
                if idx < len(times):
                    ax1.axvline(x=times[idx], color='#ef4444', linestyle='--', linewidth=2, alpha=0.7)
        
        ax1.set_xlabel('Time (seconds)', color=self.colors['text_secondary'], fontsize=11)
        ax1.set_ylabel('cwnd (MSS)', color=self.colors['text_secondary'], fontsize=11)
        ax1.set_title('Congestion Window Over Time', color=self.colors['text'], fontsize=13, fontweight='bold')
        legend1 = ax1.legend(loc='upper left')
        if legend1:
            legend1.get_frame().set_facecolor(self.colors['surface'])
            legend1.get_frame().set_edgecolor(self.colors['border'])
            for text in legend1.get_texts():
                text.set_color(self.colors['text'])
        
        # Graph 2: Throughput Over Time
        ax2 = plt.subplot(2, 2, 2)
        if packet_events:
            times = [e.get('time', 0) for e in packet_events]
            throughputs = [e.get('throughput', 0) for e in packet_events]
            node_congestions = [e.get('node_congestion', 0) for e in packet_events]
            
            ax2.plot(times, throughputs, color=self.colors['success'], linewidth=2, label='Actual Throughput')
            
            # Highlight congestion-limited periods
            congestion_limited = [i for i, c in enumerate(node_congestions) if c > 7]
            for idx in congestion_limited:
                if idx < len(times):
                    ax2.axvspan(times[max(0, idx-1)], times[min(len(times)-1, idx+1)],
                               color=self.colors['error'], alpha=0.2)
        
        ax2.set_xlabel('Time (seconds)', color=self.colors['text_secondary'], fontsize=11)
        ax2.set_ylabel('Throughput (Mbps)', color=self.colors['text_secondary'], fontsize=11)
        ax2.set_title('Throughput Over Time', color=self.colors['text'], fontsize=13, fontweight='bold')
        legend2 = ax2.legend(loc='upper left')
        if legend2:
            legend2.get_frame().set_facecolor(self.colors['surface'])
            legend2.get_frame().set_edgecolor(self.colors['border'])
            for text in legend2.get_texts():
                text.set_color(self.colors['text'])
        
        # Graph 3: Packet Delivery Timeline (Gantt chart)
        ax3 = plt.subplot(2, 2, 3)
        # Get all packets
        all_packet_ids = list(set([e.get('packet_id') for e in self.packet_events if 'packet_id' in e]))
        y_positions = {}
        for i, pid in enumerate(all_packet_ids[:20]):  # Limit to 20 packets
            y_positions[pid] = i
            packet_evts = [e for e in self.packet_events if e.get('packet_id') == pid]
            if packet_evts:
                start_time = min(e.get('time', 0) for e in packet_evts)
                end_time = max(e.get('time', 0) for e in packet_evts)
                status = packet_evts[-1].get('event_type', 'in_transit')
                
                # Color by status
                if status == 'delivered':
                    color = self.colors['success']
                elif status == 'dropped':
                    color = self.colors['error']
                else:
                    color = self.colors['accent']
                
                if end_time > start_time:
                    ax3.barh(i, end_time - start_time, left=start_time, height=0.6,
                            color=color, edgecolor=self.colors['surface'], linewidth=1)
        
        ax3.set_xlabel('Time (seconds)', color=self.colors['text_secondary'], fontsize=11)
        ax3.set_ylabel('Packet ID', color=self.colors['text_secondary'], fontsize=11)
        ax3.set_title('Packet Delivery Timeline', color=self.colors['text'], fontsize=13, fontweight='bold')
        ax3.set_yticks(range(len(all_packet_ids[:20])))
        ax3.set_yticklabels([str(pid) for pid in all_packet_ids[:20]], color=self.colors['text'])
        ax3.grid(True, alpha=0.3, color=self.colors['border'], axis='x')
        
        # Graph 4: RTT Variation
        ax4 = plt.subplot(2, 2, 4)
        if packet_events:
            times = [e.get('time', 0) for e in packet_events]
            rtts = [e.get('rtt', 0) for e in packet_events]
            
            ax4.plot(times, rtts, color='#8b5cf6', linewidth=2, marker='o', markersize=4, label='RTT')
            
            # Moving average (window size = 5)
            if len(rtts) > 5:
                moving_avg = []
                for i in range(len(rtts)):
                    window = rtts[max(0, i-2):min(len(rtts), i+3)]
                    moving_avg.append(sum(window) / len(window))
                ax4.plot(times, moving_avg, color='#fbbf24', linewidth=2, linestyle='--', label='Moving Avg')
        
        ax4.set_xlabel('Time (seconds)', color=self.colors['text_secondary'], fontsize=11)
        ax4.set_ylabel('RTT (milliseconds)', color=self.colors['text_secondary'], fontsize=11)
        ax4.set_title('RTT Variation', color=self.colors['text'], fontsize=13, fontweight='bold')
        legend4 = ax4.legend(loc='upper left')
        if legend4:
            legend4.get_frame().set_facecolor(self.colors['surface'])
            legend4.get_frame().set_edgecolor(self.colors['border'])
            for text in legend4.get_texts():
                text.set_color(self.colors['text'])

        self._style_axes([ax1, ax2, ax3, ax4])
        
        fig.subplots_adjust(hspace=0.32, wspace=0.28, left=0.08, right=0.97, top=0.92, bottom=0.08)
        
        # Embed matplotlib figure
        canvas_frame = tk.Frame(timeline_window, bg=self.colors['bg'])
        canvas_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        canvas = FigureCanvasTkAgg(fig, master=canvas_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # Buttons
        btn_frame = tk.Frame(timeline_window, bg=self.colors['bg'])
        btn_frame.pack(pady=10)
        
        def export_trace():
            import csv
            from datetime import datetime
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"packet_trace_{timestamp}.csv"
            try:
                with open(filename, 'w', newline='') as csvfile:
                    writer = csv.DictWriter(
                        csvfile,
                        fieldnames=['time', 'packet_id', 'cwnd', 'phase', 'rtt', 'event_type', 'throughput']
                    )
                    writer.writeheader()
                    writer.writerows(self.packet_events)
                messagebox.showinfo("Export Complete", f"Packet trace exported to:\n{filename}")
            except Exception as exc:
                messagebox.showerror("Export Failed", f"Unable to export data:\n{exc}")
        
        self.create_button(btn_frame, "💾 Export Trace", export_trace, self.colors['success']).pack(side=tk.LEFT, padx=5)
    
    # NEW: Show Algorithm Settings Window
    def show_algorithm_settings(self):
        """Display algorithm settings configuration window"""
        settings_window = tk.Toplevel(self.root)
        settings_window.title("⚙️ Algorithm Settings")
        settings_window.geometry("500x600")
        settings_window.configure(bg=self.colors['bg'])
        
        title = tk.Label(settings_window, text="⚙️ Congestion Control Settings", 
                        font=("Segoe UI", 16, "bold"),
                        bg=self.colors['bg'], fg=self.colors['text'])
        title.pack(pady=20)
        
        # Packet Loss Simulation
        loss_frame = tk.Frame(settings_window, bg=self.colors['panel_bg'])
        loss_frame.pack(pady=10, padx=20, fill=tk.X)
        
        tk.Label(loss_frame, text="Packet Loss Rate:", 
                bg=self.colors['panel_bg'], fg=self.colors['text'],
                font=("Segoe UI", 11)).pack(anchor='w', padx=10, pady=5)
        
        loss_var = tk.DoubleVar(value=self.packet_loss_rate)
        loss_scale = tk.Scale(loss_frame, from_=0, to=10, orient=tk.HORIZONTAL,
                             variable=loss_var, bg=self.colors['panel_bg'],
                             fg=self.colors['text'], font=("Segoe UI", 9))
        loss_scale.pack(fill=tk.X, padx=10, pady=5)
        
        loss_value_label = tk.Label(loss_frame, text=f"{self.packet_loss_rate}%",
                                  bg=self.colors['panel_bg'], fg=self.colors['accent'],
                                  font=("Segoe UI", 10, "bold"))
        loss_value_label.pack(pady=5)
        
        def update_loss_label(val):
            loss_value_label.config(text=f"{float(val):.1f}%")
        
        loss_scale.config(command=update_loss_label)
        
        # Learning Mode
        learn_frame = tk.Frame(settings_window, bg=self.colors['panel_bg'])
        learn_frame.pack(pady=10, padx=20, fill=tk.X)
        
        learn_var = tk.BooleanVar(value=self.learn_mode)
        learn_check = tk.Checkbutton(
            learn_frame,
            text="📚 Enable Learning Mode",
            variable=learn_var,
            bg=self.colors['panel_bg'],
            fg=self.colors['text'],
            selectcolor=self.colors['accent'],
            font=("Segoe UI", 10),
            activebackground=self.colors['panel_bg'],
            activeforeground=self.colors['text']
        )
        learn_check.pack(anchor='w', padx=10, pady=10)
        
        # Default Parameters
        params_frame = tk.Frame(settings_window, bg=self.colors['panel_bg'])
        params_frame.pack(pady=10, padx=20, fill=tk.X)
        
        tk.Label(params_frame, text="Default Parameters:", 
                bg=self.colors['panel_bg'], fg=self.colors['text'],
                font=("Segoe UI", 11, "bold")).pack(anchor='w', padx=10, pady=5)
        
        tk.Label(params_frame, text="Initial cwnd: 1 MSS\nInitial ssthresh: 64 MSS\nMSS: 1500 bytes",
                bg=self.colors['panel_bg'], fg=self.colors['text_secondary'],
                font=("Segoe UI", 9), justify=tk.LEFT).pack(anchor='w', padx=20, pady=5)
        
        # Apply button
        def apply_settings():
            self.packet_loss_rate = loss_var.get()
            self.learn_mode = learn_var.get()
            settings_window.destroy()
            messagebox.showinfo("Settings Applied", "Algorithm settings updated successfully")
        
        self.create_button(settings_window, "✓ Apply Settings", apply_settings, self.colors['success']).pack(pady=20)
        
    def show_node_info(self, node):
        info = f"Node: {node.name}\n"
        info += f"Type: {node.type.upper()}\n"
        info += f"Latency: {node.latency}ms\n"
        info += f"Throughput: {node.throughput}Mbps\n"
        info += f"Connections: {len(node.connections)}\n"
        info += f"Congestion Level: {node.congestion}"
        
        messagebox.showinfo(f"{node.name} Details", info)
        
    def show_metrics(self):
        if not self.nodes:
            messagebox.showwarning("No Data", "Add nodes to view metrics")
            return
            
        metrics_window = tk.Toplevel(self.root)
        metrics_window.title("TCP Congestion Metrics")
        metrics_window.geometry("520x520")
        metrics_window.configure(bg=self.colors['bg'])
        
        title = tk.Label(metrics_window, text="TCP Congestion Snapshot", 
                         font=("Segoe UI", 16, "bold"),
                         bg=self.colors['bg'], fg=self.colors['text'])
        title.pack(pady=15)
        
        info_frame = tk.Frame(metrics_window, bg=self.colors['surface'], highlightbackground=self.colors['border'], highlightthickness=1)
        info_frame.pack(fill=tk.X, padx=20, pady=10)
        
        algo_name = "Reno" if self.congestion_algorithm == "reno" else "Tahoe"
        phase_counts = self.get_phase_counts()
        avg_latency = sum(n.latency for n in self.nodes) / len(self.nodes)
        avg_throughput = sum(self.throughput_history) / len(self.throughput_history) if self.throughput_history else 0
        
        metrics = [
            ("Current Algorithm", f"TCP {algo_name}"),
            ("Traffic Load", self.traffic_load.title()),
            ("Active Packets", len(self.packets)),
            ("Avg cwnd", f"{(sum(p.cwnd for p in self.packets)/len(self.packets)):.1f} MSS" if self.packets else "0 MSS"),
            ("Avg Latency", f"{avg_latency:.1f} ms"),
            ("Avg Throughput", f"{avg_throughput:.2f} Mbps")
        ]
        
        for idx, (label, value) in enumerate(metrics):
            row = tk.Frame(info_frame, bg=self.colors['surface'])
            row.pack(fill=tk.X, padx=15, pady=4)
            tk.Label(row, text=label, fg=self.colors['text_secondary'], bg=self.colors['surface'],
                     font=("Segoe UI", 10)).pack(side=tk.LEFT)
            tk.Label(row, text=value, fg=self.colors['text'], bg=self.colors['surface'],
                     font=("Segoe UI", 11, "bold")).pack(side=tk.RIGHT)
        
        phase_frame = tk.Frame(metrics_window, bg=self.colors['bg'])
        phase_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        tk.Label(phase_frame, text="Phase Distribution", font=("Segoe UI", 13, "bold"),
                 bg=self.colors['bg'], fg=self.colors['text']).pack(anchor='w', pady=5)
        
        for phase_key, meta in self.phase_definitions.items():
            bar_frame = tk.Frame(phase_frame, bg=self.colors['bg'])
            bar_frame.pack(fill=tk.X, pady=4)
            phase_name = meta["name"]
            count = phase_counts.get(phase_key, 0)
            tk.Label(bar_frame, text=f"{phase_name}", width=18, anchor='w',
                     bg=self.colors['bg'], fg=meta["color"],
                     font=("Segoe UI", 10, "bold")).pack(side=tk.LEFT)
            progress = tk.Canvas(bar_frame, height=16, bg=self.colors['panel_bg'], highlightthickness=0)
            progress.pack(fill=tk.X, expand=True, padx=8)
            width = min(200, 20 * count)
            progress.create_rectangle(0, 0, width, 16, fill=meta["color"], outline="")
            progress.create_text(5, 8, text=f"{count} packet(s)", anchor='w',
                                 fill=self.colors['text'], font=("Segoe UI", 9))
        
        summary = tk.Label(metrics_window,
                           text="Slow Start → Congestion Avoidance → Fast Retransmit → Fast Recovery",
                           bg=self.colors['bg'], fg=self.colors['text_secondary'],
                           font=("Segoe UI", 9, "italic"))
        summary.pack(pady=10)
        
    def reset_network(self, confirm=True):
        if confirm and not messagebox.askyesno("Reset", "Clear all nodes and connections?"):
            return
            
        self.nodes.clear()
        self.connections.clear()
        self.packets.clear()
        self.simulation_running = False
        self.manual_packet_mode = False
        self.active_manual_packet_ids.clear()
        self.stop_packet_details_updates()
        self.sim_button.config(text="▶ Start Simulation", bg=self.colors['accent'])
        # NEW: Clear performance data
        self.latency_history.clear()
        self.throughput_history.clear()
        self.time_stamps.clear()
        self.performance_start_time = time.time()
         # NEW: Clear routing statistics
        self.routing_stats = {
            'total_packets': 0,
            'avg_hop_count': 0,
            'min_hops': float('inf'),
            'max_hops': 0,
            'path_history': []
        }
        # NEW: Clear packet events and reset counter
        self.packet_events.clear()
        self.packet_counter = 0
        # Clear tooltip if exists
        self.hide_tooltip()
        # Stop status updates
        if self.status_update_timer:
            self.root.after_cancel(self.status_update_timer)
        self.draw_network()
        self.status_label.config(text="Network reset")
        self.update_real_time_stats()
        self.populate_node_options()

if __name__ == "__main__":
    root = tk.Tk()
    app = CloudNetworkSimulator(root)
    root.mainloop()