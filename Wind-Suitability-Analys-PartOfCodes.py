# -*- coding: utf-8 -*-
import os
import math
import tempfile
import time
import uuid
import json
import shutil
import re
from qgis.PyQt.QtCore import QCoreApplication, Qt, QVariant
from qgis.PyQt.QtGui import QIcon, QColor
from qgis.PyQt.QtWidgets import (QAction, QMessageBox, QFileDialog, QInputDialog, QApplication, 
                                  QPushButton, QLineEdit, QVBoxLayout, QHBoxLayout, QLabel,
                                  QListWidget, QListWidgetItem, QWidget, QDoubleSpinBox, QFrame,
                                  QSpacerItem, QSizePolicy, QTableWidget, QTableWidgetItem, 
                                  QComboBox, QCheckBox, QHeaderView, QTextEdit, QProgressBar, QSpinBox, QDialog)
from qgis.core import (
    QgsProcessingFeedback,
    QgsProject, QgsRasterLayer, QgsRectangle, QgsCoordinateTransform,
    QgsWkbTypes, QgsGeometry, QgsVectorLayer, QgsFeature,
    QgsRasterShader, QgsColorRampShader, QgsSingleBandPseudoColorRenderer, QgsProcessingOutputLayerDefinition,
    QgsDistanceArea, QgsCoordinateReferenceSystem, QgsRasterFileWriter, QgsRasterDataProvider,
    QgsRasterBlock, QgsRasterPipe, QgsField, QgsRasterBandStats, QgsUnitTypes,
    QgsRasterRange,
    QgsGraduatedSymbolRenderer, QgsRendererRange, QgsSymbol, QgsClassificationMethod,
    QgsVectorFileWriter, QgsCoordinateTransformContext, QgsSimpleFillSymbolLayer,
    QgsFillSymbol, QgsSingleSymbolRenderer,
    QgsMessageLog, Qgis
)
from qgis.gui import QgsMapTool, QgsRubberBand
from qgis import processing
from .wind_suitability_dialog import WindSuitabilityDialog
from .aoi_tools import (
    PolygonMapTool,
    load_polygon_geometry_from_vector_file,
    normalize_polygon_aoi_geometry,
    is_polygonal_aoi_geometry,
    VECTOR_FILE_FILTER,
)
from .analysis_crs import get_analysis_crs_for_geometry
from .crs_reprojection_helper import is_geographic_crs, get_utm_crs_for_extent
from .scoring_raster_helper import cleanup_temp_files, check_disk_space
from qgis.analysis import QgsRasterCalculator, QgsRasterCalculatorEntry

try:
    from osgeo import gdal
    _GDAL_AVAILABLE = True
except ImportError:
    _GDAL_AVAILABLE = False
try:
    import numpy as np
    _NUMPY_AVAILABLE = True
except ImportError:
    _NUMPY_AVAILABLE = False

# ============================================================================
# GLOBAL CONSTANTS - MCA ARCHITECTURE
# ============================================================================
MCA_RESOLUTION = 100.0  # meters (fixed grid resolution - NEVER computed or inferred)
MCA_NODATA = -9999.0    # NoData value for MCA rasters

# ============================================================================
# CRS: SINGLE ANALYSIS CRS (avoid mid-workflow CRS changes)
# ============================================================================
# Use ONE metric CRS for the entire pipeline to avoid:
# - Repeated raster resampling and value/edge drift
# - Grid misalignment when combining rasters (wind, bathymetry, masks)
# - Extra reprojections and performance cost
# EPSG:3035 = ETRS89-extended / LAEA Europe: metric, equal-area, INSPIRE.
# Reproject all inputs to this once; keep all processing here; reproject only at export if needed.
PROJECT_CRS_METRIC = "EPSG:3035"

# Phase 2: Slope suitability thresholds (degrees). 0–15 suitable, 15–25 moderate, >25 unsuitable.
GOOD_SLOPE_THRESHOLD = 5.0   # slopes <= this -> suitability = 1 (stepwise model)
MODERATE_SLOPE_THRESHOLD = 15.0  # good < slope <= this -> suitability = 0.7
MAX_SLOPE_THRESHOLD = 25.0   # moderate < slope <= this -> suitability = 0.4; slope > this -> 0


class RectangleMapTool(QgsMapTool):
    def __init__(self, canvas, callback):
        super().__init__(canvas)
        self.canvas = canvas
        self.start_point = None
        self.callback = callback

    def canvasPressEvent(self, event):
        try:
            self.start_point = self.toMapCoordinates(event.pos())
        except Exception:
            self.start_point = None

    def canvasReleaseEvent(self, event):
        # Defensive guards: avoid propagating map-tool exceptions into QGIS event loop.
        if self.start_point is None:
            return
        try:
            end_point = self.toMapCoordinates(event.pos())
            rect = QgsRectangle(self.start_point, end_point)
            if rect.isEmpty() or rect.width() <= 0 or rect.height() <= 0:
                return
            self.callback(rect)
        except Exception:
            return
        finally:
            self.start_point = None


class AttributeFilterDialog(QDialog):
    """
    Dialog for filtering vector layer features by attribute values.
    Includes special handling for voltage-like fields so that users see
    clean kV labels while expressions are built against the underlying
    numeric volt values.
    """
    def __init__(self, layer, parent=None):
        super().__init__(parent)
        self.layer = layer
        self.selected_values = []
        self.setWindowTitle("Filter Settings")
        self.setMinimumWidth(400)
        self.setMinimumHeight(500)
        
        layout = QVBoxLayout(self)
        
        # Field selection
        field_label = QLabel("Select field to filter:")
        layout.addWidget(field_label)
        
        self.field_combo = QComboBox()
        layout.addWidget(self.field_combo)
        
        # List widget for values (create before connecting signals)
        list_label = QLabel("Select values to include:")
        layout.addWidget(list_label)
        
        self.value_list = QListWidget()
        layout.addWidget(self.value_list)
        
        # Now connect the signal after value_list is created
        self.field_combo.currentTextChanged.connect(self.on_field_changed)
        
        # Populate fields (this may trigger currentTextChanged)
        self.populate_fields()
        
        # Select All / Deselect All buttons
        button_layout = QHBoxLayout()
        self.btn_select_all = QPushButton("Select All")
        self.btn_deselect_all = QPushButton("Deselect All")
        self.btn_select_all.clicked.connect(self.select_all)
        self.btn_deselect_all.clicked.connect(self.deselect_all)
        button_layout.addWidget(self.btn_select_all)
        button_layout.addWidget(self.btn_deselect_all)
        button_layout.addStretch()
        layout.addLayout(button_layout)
        
        # Dialog buttons
        dialog_buttons = QHBoxLayout()
        self.btn_ok = QPushButton("OK")
        self.btn_cancel = QPushButton("Cancel")
        self.btn_ok.clicked.connect(self.accept)
        self.btn_cancel.clicked.connect(self.reject)
        dialog_buttons.addStretch()
        dialog_buttons.addWidget(self.btn_ok)
        dialog_buttons.addWidget(self.btn_cancel)
        layout.addLayout(dialog_buttons)
        
        # Load values for the first field
        if self.field_combo.count() > 0:
            self.on_field_changed(self.field_combo.currentText())
    
    def populate_fields(self):
        """Populate the field combo box with layer fields."""
        if not self.layer or not self.layer.isValid():
            return
        
        fields = self.layer.fields()
        for field in fields:
            self.field_combo.addItem(field.name(), field.name())

    def _is_voltage_field(self, field_name: str) -> bool:
        """Return True if the field name looks like a voltage field."""
        if not field_name:
            return False
        n = field_name.lower()
        return (n == "voltage") or ("volt" in n) or ("kv" in n)

    def parse_voltage_to_volts(self, v):
        """
        Returns integer volts (e.g. 110000) or None if not parseable.
        Handles:
          - 110000
          - 110 kV
          - 110000 V
          - 110000;20000  (takes max)
          - 20kV;110kV
          - empty / minor / None -> None
        """
        if v is None:
            return None
        s = str(v).strip()
        if not s:
            return None

        # split on common separators (semicolon, comma, whitespace)
        parts = re.split(r"[;,\s]+", s)
        nums = []
        for p in parts:
            p = p.strip()
            if not p:
                continue

            m = re.search(r"(\d+(?:\.\d+)?)", p)
            if not m:
                continue

            try:
                num = float(m.group(1))
            except Exception:
                continue

            # if explicitly kV in this chunk, convert to volts
            if "kv" in p.lower():
                num *= 1000.0

            nums.append(num)

        if not nums:
            return None

        volts = int(round(max(nums)))  # choose max for composite strings
        if 1 <= volts <= 1_000_000:
            return volts
        return None

    def _volts_to_label(self, volts: int) -> str:
        """Format a volt value as a human-readable kV label."""
        kv = int(round(volts / 1000.0))
        return f"{kv} kV"

    def on_field_changed(self, field_name):
        """Load unique values for the selected field and sort them."""
        if not field_name or not self.layer or not self.layer.isValid():
            return
        
        # Safety check: ensure value_list exists
        if not hasattr(self, 'value_list') or self.value_list is None:
            return
        
        self.value_list.clear()
        
        field_index = self.layer.fields().indexFromName(field_name)
        
        if field_index < 0:
            return

        # Collect unique raw values for this field
        raw_values = []
        seen = set()
        for feature in self.layer.getFeatures():
            value = feature.attribute(field_index)
            if value is None:
                continue
            key = str(value)
            if key in seen:
                continue
            seen.add(key)
            raw_values.append(value)

        qt_constants = self.get_qt_constants()

        # Special handling for voltage-like fields: show clean kV labels
        # but store numeric volts for filter expression building.
        if self._is_voltage_field(field_name):
            unique_volts = set()
            for value in raw_values:
                volts = self.parse_voltage_to_volts(value)
                if volts is not None:
                    unique_volts.add(volts)

            for volts in sorted(unique_volts):
                label = self._volts_to_label(volts)
                item = QListWidgetItem(label)
                item.setFlags(item.flags() | qt_constants['ItemIsUserCheckable'])
                item.setCheckState(qt_constants['Checked'])
                # Store numeric volts in UserRole for later use
                try:
                    if hasattr(Qt, 'ItemDataRole'):
                        item.setData(Qt.ItemDataRole.UserRole, volts)
                    else:
                        item.setData(Qt.UserRole, volts)
                except Exception:
                    item.setData(256, volts)  # UserRole = 256
                self.value_list.addItem(item)
            return

        # Generic behaviour for non-voltage fields: show unique string values.
        unique_strings = set()
        for value in raw_values:
            s = str(value).strip()
            if s == "":
                continue
            unique_strings.add(s)

        display_values = sorted(unique_strings)

        for value in display_values:
            item = QListWidgetItem(value)
            item.setFlags(item.flags() | qt_constants['ItemIsUserCheckable'])
            item.setCheckState(qt_constants['Checked'])
            # Store original string value as data for later filter construction
            try:
                if hasattr(Qt, 'ItemDataRole'):
                    item.setData(Qt.ItemDataRole.UserRole, value)
                else:
                    item.setData(Qt.UserRole, value)
            except Exception:
                item.setData(256, value)  # UserRole = 256
            self.value_list.addItem(item)
    
    def get_qt_constants(self):
        """Safely get Qt constants."""
        try:
            from qgis.PyQt.QtCore import Qt
            try:
                if hasattr(Qt, 'ItemFlag'):
                    item_is_user_checkable = Qt.ItemFlag.ItemIsUserCheckable
                elif hasattr(Qt, 'ItemIsUserCheckable'):
                    item_is_user_checkable = Qt.ItemIsUserCheckable
                else:
                    item_is_user_checkable = 0x0001
            except (AttributeError, TypeError):
                item_is_user_checkable = 0x0001
            
            try:
                if hasattr(Qt, 'CheckState'):
                    checked = Qt.CheckState.Checked
                else:
                    checked = Qt.Checked
            except (AttributeError, TypeError):
                checked = 2
            
            return {
                'ItemIsUserCheckable': item_is_user_checkable,
                'Checked': checked
            }
        except ImportError:
            return {
                'ItemIsUserCheckable': 0x0001,
                'Checked': 2
            }
    
    def select_all(self):
        """Select all items in the list."""
        qt_constants = self.get_qt_constants()
        for i in range(self.value_list.count()):
            item = self.value_list.item(i)
            if item:
                item.setCheckState(qt_constants['Checked'])
    
    def deselect_all(self):
        """Deselect all items in the list."""
        qt_constants = self.get_qt_constants()
        try:
            from qgis.PyQt.QtCore import Qt
            if hasattr(Qt, 'CheckState'):
                unchecked = Qt.CheckState.Unchecked
            else:
                unchecked = Qt.Unchecked
        except:
            unchecked = 0
        
        for i in range(self.value_list.count()):
            item = self.value_list.item(i)
            if item:
                item.setCheckState(unchecked)
    
    def get_filter_expression(self):
        """
        Get the SQL subset string for the selected values.
        Returns None if no filter should be applied.
        """
        if not self.layer or not self.layer.isValid():
            return None
        
        field_name = self.field_combo.currentText()
        if not field_name:
            return None

        # Resolve field definition
        fields = self.layer.fields()
        field_index = fields.indexFromName(field_name)
        if field_index < 0:
            return None
        fld = fields[field_index]

        selected_values = []
        qt_constants = self.get_qt_constants()

        for i in range(self.value_list.count()):
            item = self.value_list.item(i)
            if not item:
                continue
            if item.checkState() != qt_constants['Checked']:
                continue

            # Prefer stored UserRole data; fall back to display text.
            try:
                if hasattr(Qt, 'ItemDataRole'):
                    data_val = item.data(Qt.ItemDataRole.UserRole)
                else:
                    data_val = item.data(Qt.UserRole)
            except Exception:
                data_val = item.data(256)  # UserRole = 256
            if data_val is None:
                data_val = item.text()
            selected_values.append(data_val)

        if not selected_values:
            return None

        # Voltage-like fields: assume stored UserRole is numeric volts.
        if self._is_voltage_field(field_name):
            volts = []
            for v in selected_values:
                if isinstance(v, (int, float)):
                    volts.append(int(round(v)))
                else:
                    parsed = self.parse_voltage_to_volts(v)
                    if parsed is not None:
                        volts.append(parsed)
            if not volts:
                return None
            unique_volts = sorted(set(volts))
            return f'"{field_name}" IN ({", ".join(str(v) for v in unique_volts)})'

        # Non-voltage fields: honour field numeric/text type.
        if fld.isNumeric():
            nums = []
            for v in selected_values:
                try:
                    num = float(v)
                except Exception:
                    continue
                nums.append(num)
            if not nums:
                return None
            unique_nums = sorted(set(nums))
            formatted = []
            for num in unique_nums:
                if float(num).is_integer():
                    formatted.append(str(int(num)))
                else:
                    formatted.append(str(num))
            return f'"{field_name}" IN ({", ".join(formatted)})'
        else:
            strs = []
            for v in selected_values:
                s = "" if v is None else str(v)
                strs.append(s.replace("'", "''"))
            if not strs:
                return None
            unique_strs = sorted(set(strs))
            return f'"{field_name}" IN (' + ", ".join(f"'{s}'" for s in unique_strs) + ")"


class WindSuitability:
    def __init__(self, iface):
        self.iface = iface
        self.canvas = iface.mapCanvas()
        self.plugin_dir = os.path.dirname(__file__)
        self.dlg = None
        self.action = None
        self.tool_rectangle = None
        self.tool_polygon = None
        self.aoi_extent = None  # QgsRectangle in analysis CRS (see self.analysis_crs)
        self.analysis_crs = None  # QgsCoordinateReferenceSystem chosen from AOI; not map canvas CRS
        # self.rubber_band = None  # Remove this
        self._last_rubber_band = None
        self.germany_wind_path = os.path.join(self.plugin_dir, "data", "germany_windspeed.tif")
        self.bathymetry_path = os.path.join(self.plugin_dir, "data", "germany_bathymetry.tif")
        self.wind_result_path = None
        self.wind_master_path = None  # Single source of truth set after wind clipping
        self.depth_result_path = None
        self.prospect_result_path = None
        self.spatial_filter_result_path = None
        self.spatial_filter_exclude_mask_path = None
        self._gdal_raster_path_cache = {}  # source_abs -> reusable temp/openable path
        # Constraint layers functionality removed - using excluded/preferred layers instead
        # Unified spatial filter rows (each row has a role: Exclude / Include)
        self.spatial_filter_rows = []
        self.excluded_layer_rows = []  # Legacy view: subset of spatial_filter_rows with role == "Exclude"
        self._excluded_layout_spacer = None
        self.preferred_layer_rows = []  # Legacy view: subset of spatial_filter_rows with role == "Include"
        self._preferred_layout_spacer = None
        self.decision_making_layers = []  # Store decision making criteria layers
        self.mca_reference_raster = None  # IMMUTABLE reference raster grid created from AOI only (SINGLE SOURCE OF TRUTH)
        self.mca_grid_layer = None  # IMMUTABLE reference raster grid created from AOI only (SINGLE SOURCE OF TRUTH)
        self.mca_data_matrix = []  # Store the MCA data matrix (grid_id, criterion_name, raw_value, weight, role)
        self.grid_sampling_method = "mean"  # "mean" = zonal mean per cell, "centroid" = sample at cell centroid
        # User-defined AOI (single geometry / single-feature layer) — never mixed with pipeline outputs
        self.current_aoi = None  # QgsGeometry in analysis CRS (canonical AOI polygon)
        self.user_aoi_layer = None  # memory QgsVectorLayer, exactly one polygon feature
        self.final_aoi_layer = None  # MCA / exclusion pipeline final polygon only (not user-drawn AOI)
        self.prospect_polygon_cache = None  # last-resort resolved prospect layer; does not replace final_aoi_layer
        self.mca_output_dir = None  # Stable directory for MCA layer outputs
        self.output_dir = None  # User output folder (parent)
        self.results_dir = None  # output_dir/results - final outputs only
        self.temp_dir = None  # output_dir/temp - intermediate files only
        self.aoi_master_layer = None  # SINGLE SOURCE OF TRUTH: Real vector polygon layer for AOI (created from extent)
        self.clipped_dem_path = None  # Phase 2: optional clipped DEM from workflow (reused for slope; no redundant clipping)
        self.DEBUG_SPATIAL = False  # Set True to enable minimal [SpatialFilter] debug logs only
        # Transient per-run proximity paths; cleared when AOI/session resets.
        self._current_vector_converted_raster_path = None
        self._current_distance_raster_path = None
        self._current_suitability_raster_path = None


    def tr(self, message):
        return QCoreApplication.translate('WindSuitability', message)

    def _log_core_raster_state(self, prefix):
        """Debug snapshot for core rasters that must never be replaced by spatial filtering."""
        QgsMessageLog.logMessage(
            "[DEBUG] {} core rasters: wind_result_path='{}', depth_result_path='{}', clipped_dem_path='{}', prospect_result_path='{}', wind_master_path='{}'".format(
                prefix,
                getattr(self, "wind_result_path", None),
                getattr(self, "depth_result_path", None),
                getattr(self, "clipped_dem_path", None),
                getattr(self, "prospect_result_path", None),
                getattr(self, "wind_master_path", None),
            ),
            "WindSuitability",
            Qgis.Info,
        )

    def initGui(self):
        icon_path = ':/plugins/wind_suitability/icon.png'
        self.action = QAction(QIcon(icon_path), self.tr("Wind Suitability Analysis"), self.iface.mainWindow())
        self.action.triggered.connect(self.run)
        self.iface.addPluginToMenu(self.tr("&Wind Suitability"), self.action)
        self.iface.addToolBarIcon(self.action)

    def unload(self):
        try:
            if self.tool_rectangle and self.canvas.mapTool() == self.tool_rectangle:
                self.canvas.unsetMapTool(self.tool_rectangle)
        except Exception:
            pass
        try:
            if self.tool_polygon and self.canvas.mapTool() == self.tool_polygon:
                self.canvas.unsetMapTool(self.tool_polygon)
        except Exception:
            pass
        self.clear_rubber_band()
        self._last_rubber_band = None
        # Clean up temporary files when plugin is unloaded
        self.cleanup_temp_files()
        self.iface.removePluginMenu(self.tr("&Wind Suitability"), self.action)
        self.iface.removeToolBarIcon(self.action)

    def clear_rubber_band(self):
        if self._last_rubber_band:
            try:
                if self.canvas and hasattr(self.canvas, 'scene') and self.canvas.scene():
                    self._last_rubber_band.reset(QgsWkbTypes.PolygonGeometry)
                    self.canvas.scene().removeItem(self._last_rubber_band)
            except Exception:
                pass
            self._last_rubber_band = None

    # Fixed output filenames: only results/ and temp/, no nested subfolders
    PROSPECT_AREA_GPKG = "prospect_area.gpkg"
    PROSPECT_RASTER_TIF = "prospect_area.tif"
    WIND_ANALYSIS_TIF = "wind_analysis.tif"
    DEPTH_ANALYSIS_TIF = "depth_analysis.tif"
    SPATIAL_FILTERED_TIF = "spatial_filtered.tif"
    MERGED_EXCLUDE_MASK_TIF = "merged_exclude_mask.tif"
    INCLUDE_MASK_TIF = "include_mask.tif"
    RASTER_INPUT_FILE_FILTER = (
        "Raster files (*.tif *.tiff *.TIF *.TIFF *.vrt *.VRT *.img *.IMG);;"
        "All files (*.*)"
    )

    def ensure_output_dirs(self, base_path):
        """
        Set output root and create results/temp subdirs. User-selected directory is the root (no extra folder).
        Creates ONLY: output_dir/results and output_dir/temp. No nested subfolders (no wind/, bathymetry/, spatial/, etc.).
        - If base_path is a directory: use it as output_dir.
        - If base_path is a file: use its parent directory as output_dir.
        - If that directory is named "results" or "temp", go up until we have the true root.
        """
        if not base_path or not str(base_path).strip():
            return
        base_path = os.path.abspath(str(base_path).strip())
        # Treat as file path if it exists as file, or if it looks like a file (e.g. .tif, .gpkg) so we never use it as output_dir
        looks_like_file = base_path.lower().endswith(('.tif', '.tiff', '.gpkg', '.shp', '.geojson', '.json', '.nc', '.img'))
        if os.path.isfile(base_path) or looks_like_file:
            root = os.path.dirname(base_path)
        else:
            root = base_path
        root = os.path.abspath(root)
        # Never use .../results or .../temp as output_dir; go up to the user's root
        while root and os.path.basename(root) in ("results", "temp"):
            parent = os.path.dirname(root)
            if parent == root:
                break
            root = parent
        if not root:
            return
        try:
            os.makedirs(root, exist_ok=True)
        except Exception:
            return
        self.output_dir = root
        self.results_dir = os.path.join(root, "results")
        self.temp_dir = os.path.join(root, "temp")
        try:
            os.makedirs(self.results_dir, exist_ok=True)
            os.makedirs(self.temp_dir, exist_ok=True)
        except Exception:
            pass

    def _release_and_remove_path(self, path):
        """Release QGIS layers using this path and remove file so it can be overwritten. Returns True if safe to write."""
        if not path:
            return True
        norm = self._normalize_path(path)
        for layer in list(QgsProject.instance().mapLayers().values()):
            try:
                src = (layer.dataProvider().dataSourceUri() if getattr(layer, "dataProvider", None) else None) or getattr(layer, "source", None) or (layer.source() if hasattr(layer, "source") else None)
                if not src:
                    continue
                src_path = (src.split("|")[0] if "|" in src else src).strip()
                src_norm = self._normalize_path(src_path)
                if src_norm == norm or norm in src_norm or src_norm in norm:
                    QgsProject.instance().removeMapLayer(layer.id())
                    break
            except Exception:
                pass
        if os.path.exists(norm):
            try:
                os.remove(norm)
                return True
            except Exception:
                return False
        return True

    def _remove_raster_layers_for_disk_path(self, path):
        """Remove QgsRasterLayer instances using this file so re-add reads fresh data from disk (avoids stale cache)."""
        if not path:
            return
        try:
            norm = self._normalize_path(path)
            abs_target = os.path.normcase(os.path.abspath(norm.replace("/", os.sep)))
        except Exception:
            try:
                abs_target = os.path.normcase(os.path.abspath(path))
            except Exception:
                return
        for lid in list(QgsProject.instance().mapLayers().keys()):
            lyr = QgsProject.instance().mapLayer(lid)
            if not isinstance(lyr, QgsRasterLayer):
                continue
            try:
                src = lyr.source() or ""
                src_path = (src.split("|")[0]).strip().strip('"')
                abs_src = os.path.normcase(os.path.abspath(self._normalize_path(src_path).replace("/", os.sep)))
                if abs_src == abs_target:
                    QgsProject.instance().removeMapLayer(lid)
            except Exception:
                continue
        try:
            QCoreApplication.processEvents()
        except Exception:
            pass

    def _refresh_map_after_raster_layer_added(self, raster_layer):
        try:
            if raster_layer:
                raster_layer.triggerRepaint()
            if getattr(self, "iface", None) and self.iface.mapCanvas():
                self.iface.mapCanvas().refresh()
        except Exception:
            pass

    def get_plugin_temp_dir(self):
        """Return plugin temp directory for intermediate files; fallback to system temp."""
        if self.temp_dir and os.path.isdir(self.temp_dir):
            return self._normalize_path(self.temp_dir)
        return self._normalize_path(tempfile.gettempdir())

    def get_plugin_results_dir(self):
        """Return plugin results directory for final outputs; fallback to output_dir or temp."""
        if self.results_dir and os.path.isdir(self.results_dir):
            return self._normalize_path(self.results_dir)
        if self.output_dir and os.path.isdir(self.output_dir):
            return self._normalize_path(self.output_dir)
        return self.get_plugin_temp_dir()

    def _output_timestamp(self):
        return time.strftime("%Y%m%d_%H%M%S")

    def _safe_to_float(self, value):
        """Convert QVariant/locale-formatted numeric to float, or None on failure."""
        if value is None:
            return None
        try:
            if isinstance(value, QVariant):
                if value.isNull():
                    return None
                if value.canConvert(QVariant.Double):
                    return float(value.toDouble()[0])
                value = str(value)
            if isinstance(value, str):
                s = value.strip()
                if not s:
                    return None
                s = s.replace(",", ".")
                return float(s)
            return float(value)
        except Exception:
            return None

    def _unique_map_layer_name(self, base_name):
        """Display name for new map layers — avoids TOC clashes (timestamp suffix)."""
        return self.tr("{0} ({1})").format(base_name, self._output_timestamp())

    def _resolve_output_raster_path(self, user_text, default_stem, suffix=".tif"):
        """
        Respect user path from line edit when provided.
        If empty, use results (or temp) with a timestamped default name.
        If user_text is a directory, place default_stem_TIMESTAMP.tif inside it.
        """
        v = (user_text or "").strip()
        self.ensure_output_dirs(self.output_dir or self.get_plugin_temp_dir())
        base_dir = self.get_plugin_results_dir()
        if not v:
            return self._normalize_path(os.path.join(base_dir, f"{default_stem}_{self._output_timestamp()}{suffix}"))
        v = self._normalize_path(v)
        if os.path.isdir(v):
            return self._normalize_path(os.path.join(v, f"{default_stem}_{self._output_timestamp()}{suffix}"))
        d = os.path.dirname(v)
        if d and not os.path.exists(d):
            try:
                os.makedirs(d, exist_ok=True)
            except OSError:
                pass
        return v

    def reset_analysis_session(self):
        """Clear stored AOI/raster state for a clean run (optional UI button)."""
        self._remove_user_aoi_layers_from_project()
        self._clear_transient_proximity_state(remove_layers=True)
        self.clear_rubber_band()
        self.current_aoi = None
        self.user_aoi_layer = None
        self.aoi_extent = None
        self.analysis_crs = None
        self.final_aoi_layer = None
        self.prospect_polygon_cache = None
        self.aoi_master_layer = None
        self.wind_result_path = None
        self.wind_master_path = None
        self.depth_result_path = None
        self.prospect_result_path = None
        self.clipped_dem_path = None
        self._gdal_raster_path_cache = {}
        self.mca_reference_raster = None
        self.mca_grid_layer = None
        self.mca_data_matrix = []
        try:
            self.iface.messageBar().pushMessage(
                "Wind Suitability",
                self.tr("Session state reset (AOI and in-memory paths). Files on disk are unchanged."),
                level=Qgis.Info,
                duration=5,
            )
        except Exception:
            pass

    def _remove_user_aoi_layers_from_project(self):
        """Remove any AOI layer previously added to the project (tagged wind_plugin_user_aoi)."""
        try:
            proj = QgsProject.instance()
            to_remove = []
            for lid, layer in proj.mapLayers().items():
                if isinstance(layer, QgsVectorLayer):
                    p = layer.customProperty("wind_plugin_user_aoi")
                    if p is True or p == "true" or p == "True":
                        to_remove.append(lid)
            for lid in to_remove:
                proj.removeMapLayer(lid)
        except Exception:
            pass

    def _prepare_new_aoi_definition(self):
        """
        Before the user defines a new AOI: clear the previous user AOI from memory and map
        so only the next geometry is used in analysis.
        """
        self._remove_user_aoi_layers_from_project()
        self._clear_transient_proximity_state(remove_layers=True)
        self.clear_rubber_band()
        self.current_aoi = None
        self.user_aoi_layer = None
        self.aoi_master_layer = None
        self.aoi_extent = None
        self.analysis_crs = None
        self.invalidate_all_excluded_layer_caches()

    def _clear_transient_proximity_state(self, remove_layers=False):
        """
        Clear per-run vector->distance raster paths and optionally remove transient
        proximity/conversion layers from the map when AOI changes.
        """
        self._current_vector_converted_raster_path = None
        self._current_distance_raster_path = None
        self._current_suitability_raster_path = None
        if not remove_layers:
            return
        try:
            proj = QgsProject.instance()
            to_remove = []
            for lid, layer in proj.mapLayers().items():
                if isinstance(layer, QgsRasterLayer):
                    p = layer.customProperty("wind_plugin_transient_proximity")
                    if p is True or p == "true" or p == "True":
                        to_remove.append(lid)
            for lid in to_remove:
                proj.removeMapLayer(lid)
        except Exception:
            pass

    def get_user_aoi_layer(self):
        """Single-feature memory layer for the current user AOI, or None."""
        if self.user_aoi_layer and self.user_aoi_layer.isValid() and self.user_aoi_layer.featureCount() > 0:
            return self.user_aoi_layer
        return None

    def _aoi_geometry_cache_key(self):
        """
        Stable string for cache invalidation when AOI changes (extent alone is not enough).
        Uses analysis-CRS geometry WKT from self.current_aoi.
        """
        g = self.current_aoi
        if not g or g.isEmpty():
            return ""
        try:
            return g.asWkt()
        except Exception:
            try:
                return g.exportToWkt()
            except Exception:
                return ""

    def cleanup_old_files(self, output_dir):
        """Clean up old prospect polygon files in the output directory (prospect_area.gpkg and legacy prospect_polygon*.gpkg)."""
        import glob
        try:
            for name in [self.PROSPECT_AREA_GPKG] + ["prospect_polygon*.gpkg"]:
                if "*" in name:
                    old_files = glob.glob(os.path.join(output_dir, name))
                else:
                    p = os.path.join(output_dir, name)
                    old_files = [p] if os.path.exists(p) else []
                for old_file in old_files:
                    try:
                        os.remove(old_file)
                    except Exception:
                        pass
        except Exception:
            pass

    def cleanup_temp_files(self):
        """
        When the plugin is closed or reloaded: delete files in the temp directory that start with 'wind_plugin_'.
        Do NOT delete files in the results directory.
        """
        import glob
        try:
            cleaned_count = 0
            # Clean plugin temp dir (output_folder/temp) if it exists
            if self.temp_dir and os.path.isdir(self.temp_dir):
                for f in glob.glob(os.path.join(self.temp_dir, "wind_plugin_*")):
                    try:
                        if os.path.isfile(f):
                            os.remove(f)
                            cleaned_count += 1
                    except Exception:
                        pass
            # Also clean system temp of known plugin patterns (for backwards compatibility)
            temp_dir = tempfile.gettempdir()
            for pattern in ["wind_plugin_*", "powerline_reprojected_*.gpkg", "powerline_buffer_*.gpkg",
                           "prospect_polygon_auto*.gpkg", "aoi_clipped_*.gpkg", "protected_aoi_clipped_*.gpkg"]:
                for temp_file in glob.glob(os.path.join(temp_dir, pattern)):
                    try:
                        if os.path.isfile(temp_file):
                            os.remove(temp_file)
                            cleaned_count += 1
                    except Exception:
                        pass
            return cleaned_count
        except Exception:
            return 0

    def create_aoi_layer_from_geometry(self, geometry, source_crs):
        """
        Create the AOI_MASTER memory layer from a polygon geometry.
        All AOI inputs (rectangle, digitized polygon, file import) must funnel through this.

        Args:
            geometry: QgsGeometry in source_crs (polygon or multipolygon).
            source_crs: QgsCoordinateReferenceSystem of the geometry.

        Returns:
            QgsVectorLayer with a single polygon feature in the analysis CRS.
        """
        if not geometry or geometry.isEmpty():
            raise RuntimeError("AOI geometry is empty.")

        if not source_crs or not source_crs.isValid():
            raise RuntimeError("Invalid CRS for AOI geometry.")

        g = normalize_polygon_aoi_geometry(QgsGeometry(geometry))
        if g.isEmpty():
            raise RuntimeError("AOI geometry is empty after makeValid().")

        if not is_polygonal_aoi_geometry(g):
            raise RuntimeError("AOI must be polygon or multipolygon geometry.")

        try:
            target_crs = get_analysis_crs_for_geometry(g, source_crs)
        except ValueError as e:
            raise RuntimeError(str(e)) from e
        transform = QgsCoordinateTransform(source_crs, target_crs, QgsProject.instance())
        try:
            g.transform(transform)
        except Exception as e:
            raise RuntimeError(f"Could not reproject AOI to analysis CRS: {e}") from e

        if g.isEmpty():
            raise RuntimeError("AOI geometry is empty after reprojection.")

        aoi_layer = QgsVectorLayer(
            f"Polygon?crs={target_crs.authid()}",
            "AOI_MASTER",
            "memory"
        )
        feat = QgsFeature()
        feat.setGeometry(g)
        aoi_layer.dataProvider().addFeature(feat)
        aoi_layer.updateExtents()

        if aoi_layer.featureCount() != 1:
            raise RuntimeError("AOI layer creation failed.")

        return aoi_layer

    def create_aoi_layer_from_extent(self, extent, target_crs):
        """
        Legacy helper: extent corners are expressed in target_crs.
        Delegates to create_aoi_layer_from_geometry.
        """
        if not extent or extent.width() <= 0 or extent.height() <= 0:
            raise RuntimeError("Invalid AOI extent")
        if not target_crs or not target_crs.isValid():
            raise RuntimeError("Invalid target CRS for AOI")
        return self.create_aoi_layer_from_geometry(QgsGeometry.fromRect(extent), target_crs)

    def _validate_vector_for_processing(self, layer, context=""):
        """
        Hard validation before ANY spatial operation.
        Returns True if safe, False otherwise (and shows message).
        """
        if not layer or not layer.isValid():
            QMessageBox.warning(self.dlg, "Invalid Layer",
                                f"{context}: layer is invalid.")
            return False

        if layer.featureCount() == 0:
            QMessageBox.warning(self.dlg, "Empty Layer",
                                f"{context}: layer contains no features.")
            return False

        if layer.extent().isEmpty() or layer.extent().isNull():
            QMessageBox.warning(self.dlg, "Invalid Extent",
                                f"{context}: layer extent is empty.")
            return False

        return True

    def _validate_intersection_with_aoi(self, layer, context=""):
        """
        Ensure vector layer intersects the current user AOI before difference/rasterization.
        Single source of truth: get_user_aoi_layer() (not prospect/final pipeline layers).
        """
        aoi_layer = self.get_user_aoi_layer()

        if not aoi_layer or not aoi_layer.isValid():
            QMessageBox.critical(
                self.dlg,
                "AOI Error",
                f"{context}: No valid Area of Interest.\n\n"
                "Define an AOI (rectangle, polygon, or file) before running spatial filters.",
            )
            return False

        layer_extent = layer.extent()
        aoi_extent = aoi_layer.extent()
        
        # Check CRS compatibility - if different CRS, try to transform layer extent
        if layer.crs() != aoi_layer.crs():
            try:
                transform = QgsCoordinateTransform(layer.crs(), aoi_layer.crs(), QgsProject.instance())
                layer_extent = transform.transformBoundingBox(layer_extent)
            except Exception:
                pass  # If transformation fails, continue with original extents
        
        if not layer_extent.intersects(aoi_extent):
            # Provide detailed error message with extent information
            QMessageBox.warning(
                self.dlg, 
                "No Intersection",
                f"{context}: Layer does not intersect AOI.\n\n"
                f"Layer: '{layer.name()}' (CRS: {layer.crs().authid()})\n"
                f"Layer extent: X=[{layer_extent.xMinimum():.2f}, {layer_extent.xMaximum():.2f}], "
                f"Y=[{layer_extent.yMinimum():.2f}, {layer_extent.yMaximum():.2f}]\n\n"
                f"AOI: '{aoi_layer.name()}' (CRS: {aoi_layer.crs().authid()})\n"
                f"AOI extent: X=[{aoi_extent.xMinimum():.2f}, {aoi_extent.xMaximum():.2f}], "
                f"Y=[{aoi_extent.yMinimum():.2f}, {aoi_extent.yMaximum():.2f}]\n\n"
                f"Please ensure your layer overlaps with the selected Area of Interest.\n"
                f"If the CRS are different, the layer will be reprojected during processing."
            )
            return False

        return True

    def clip_polygon_to_aoi(self, input_layer, layer_name, output_suffix=""):
        """
        Clip any polygon layer to the AOI extent for better performance
        This is a crucial optimization that prevents processing unnecessary data
        """
        import processing
        import tempfile
        import uuid

        if not self.aoi_extent:
            QMessageBox.warning(self.dlg, "No AOI", "Please select an Area of Interest first.")
            return None

        # Create unique temporary file name
        unique_id = str(uuid.uuid4())[:8]
        temp_output = os.path.join(tempfile.gettempdir(), f"aoi_clipped_{unique_id}_{output_suffix}.gpkg")

        # Clean up any existing file
        if os.path.exists(temp_output):
            try:
                os.remove(temp_output)
            except Exception:
                pass

        try:
            # User AOI only (never pipeline / MCA final polygons)
            aoi_layer = self.get_user_aoi_layer()
            if not aoi_layer:
                QMessageBox.warning(self.dlg, "No AOI", "Please select an Area of Interest first.")
                return None

            # FAST STEP 0: Pre-filter by AOI extent BEFORE heavy fixgeometries on huge layers.
            # This dramatically reduces work for very large datasets (e.g., 1.7 GB GeoPackages).
            working_layer = input_layer
            try:
                layer_crs = input_layer.crs() if hasattr(input_layer, "crs") else None
                aoi_crs = aoi_layer.crs()
                if layer_crs and aoi_crs and layer_crs.isValid() and aoi_crs.isValid() and layer_crs == aoi_crs:
                    preclip_path = os.path.join(
                        tempfile.gettempdir(),
                        f"aoi_preclip_{unique_id}_{output_suffix}.gpkg"
                    )
                    processing.run("native:extractbyextent", {
                        "INPUT": input_layer,
                        "EXTENT": aoi_layer.extent(),
                        "CLIP": False,  # just filter features by bbox, no geometry cut
                        "OUTPUT": preclip_path,
                    })
                    if os.path.exists(preclip_path):
                        preclip_layer = QgsVectorLayer(preclip_path, "Preclip AOI", "ogr")
                        if preclip_layer.isValid():
                            working_layer = preclip_layer
            except Exception:
                # If pre-filtering fails for any reason, fall back to original layer
                working_layer = input_layer

            # Fix geometries first to avoid clipping errors (especially for GeoJSON)
            fixed_input_path = os.path.join(tempfile.gettempdir(), f"fixed_before_clip_{unique_id}.gpkg")
            try:
                processing.run("native:fixgeometries", {
                    'INPUT': working_layer,
                    'OUTPUT': fixed_input_path
                })
                if os.path.exists(fixed_input_path):
                    fixed_layer = QgsVectorLayer(fixed_input_path, "Fixed Input", "ogr")
                    if fixed_layer.isValid():
                        working_layer = fixed_layer
            except Exception:
                # If fix fails, continue with original layer
                pass

            # Clip the input layer to AOI
            processing.run("native:clip", {
                'INPUT': working_layer,
                'OVERLAY': aoi_layer,
                'OUTPUT': temp_output
            })

            if os.path.exists(temp_output):
                clipped_layer = QgsVectorLayer(temp_output, f"{layer_name} (AOI Clipped)", "ogr")
                if clipped_layer.isValid():
                    # Count features before and after clipping
                    original_count = working_layer.featureCount()
                    clipped_count = clipped_layer.featureCount()

                    # Show progress information
                    self.show_progress_message(f"AOI Clipping Complete", 
                                             f"Successfully clipped {layer_name} to AOI.\n"
                                             f"Original features: {original_count}\n"
                                             f"Features in AOI: {clipped_count}")
                    return clipped_layer
                else:
                    QMessageBox.warning(self.dlg, "Clipping Error", f"Failed to load clipped {layer_name}")
                    return None
            else:
                QMessageBox.warning(self.dlg, "Clipping Error", f"Failed to create clipped {layer_name}")
                return None
                
        except Exception as e:
            QMessageBox.critical(self.dlg, "Clipping Error", f"Error clipping {layer_name} to AOI: {str(e)}")
            return None

    def show_progress_message(self, title, message, message_type="info"):
        """
        Show progress messages with different types
        """
        if message_type == "info":
            QMessageBox.information(self.dlg, title, message)
        elif message_type == "warning":
            QMessageBox.warning(self.dlg, title, message)
        elif message_type == "critical":
            QMessageBox.critical(self.dlg, title, message)
        else:
            QMessageBox.information(self.dlg, title, message)

    def debug_layer_info(self, layer, layer_name):
        """
        Debug function to show detailed layer information
        """
        if not layer or not layer.isValid():
            return f"{layer_name}: Invalid layer"
        
        try:
            feature_count = layer.featureCount()
            extent = layer.extent()
            crs = layer.crs().authid()
            
            # Check if layer has features
            if feature_count == 0:
                return f"{layer_name}: No features\nCRS: {crs}\nExtent: {extent.toString()}"
            
            # Get first feature to check geometry (fixed API call)
            features = list(layer.getFeatures())
            if features:
                geom = features[0].geometry()
                if geom and not geom.isEmpty():
                    geom_type = geom.type()
                    return f"{layer_name}: {feature_count} features\nCRS: {crs}\nExtent: {extent.toString()}\nGeometry type: {geom_type}"
                else:
                    return f"{layer_name}: {feature_count} features but geometries are empty"
            else:
                return f"{layer_name}: {feature_count} features but cannot access them"
                
        except Exception as e:
            return f"{layer_name}: Error getting info - {str(e)}"

    def manual_cleanup_temp_files(self):
        """Manual cleanup of temporary files - can be called by user"""
        cleaned_count = self.cleanup_temp_files()
        if cleaned_count > 0:
            QMessageBox.information(self.dlg, "Cleanup Complete", 
                                  f"Cleaned up {cleaned_count} temporary files.")
        else:
            QMessageBox.information(self.dlg, "Cleanup Complete", 
                                  "No temporary files found to clean up.")

    def run(self):
        self.clear_rubber_band()
        # (Do NOT connect to QgsProject.instance().cleared)
        if not self.dlg:
            self.dlg = WindSuitabilityDialog()
            self.dlg.btnDownloadWind.clicked.connect(self.clip_wind_raster)
            self.dlg.btnDownloadDepth.clicked.connect(self.clip_bathymetry_raster)
            self.dlg.btnRunAnalysis.clicked.connect(self.run_analysis)
            self.dlg.btnRunDepthAnalysis.clicked.connect(self.run_depth_analysis)
            self.dlg.btnProspectArea.clicked.connect(self.find_prospect_area)
            self.dlg.btnProspectPolygon.clicked.connect(self.polygonize_prospect_area)
            self.dlg.btnBrowseWindPath.clicked.connect(self.browse_wind_path)
            self.dlg.btnBrowseBathymetryPath.clicked.connect(self.browse_bathymetry_path)
            btn_wi = getattr(self.dlg, "btn_browse_wind_input", None)
            if btn_wi is not None:
                btn_wi.clicked.connect(self.browse_wind_input_raster)
            btn_wl = getattr(self.dlg, "btn_wind_input_layer", None)
            if btn_wl is not None:
                btn_wl.clicked.connect(self.pick_wind_input_from_map_layer)
            btn_di = getattr(self.dlg, "btn_browse_dem_input", None)
            if btn_di is not None:
                btn_di.clicked.connect(self.browse_dem_input_raster)
            btn_dl = getattr(self.dlg, "btn_dem_input_layer", None)
            if btn_dl is not None:
                btn_dl.clicked.connect(self.pick_dem_input_from_map_layer)
            self.dlg.btnBrowseWindAnalysis.clicked.connect(self.browse_wind_analysis_path)
            self.dlg.btnBrowseDepthAnalysis.clicked.connect(self.browse_depth_analysis_path)
            self.dlg.btnBrowseProspectPath.clicked.connect(self.browse_prospect_path)
            combo_aoi = getattr(self.dlg, "combo_aoi_source", None)
            if combo_aoi is not None:
                combo_aoi.activated.connect(self._on_aoi_method_activated)
                combo_aoi.currentIndexChanged.connect(self._on_aoi_source_changed)
                self._on_aoi_source_changed(combo_aoi.currentIndex())
            btn_reset = getattr(self.dlg, "btnResetAnalysis", None)
            if btn_reset is not None:
                btn_reset.clicked.connect(self.reset_analysis_session)
            # Powerlines functionality has been integrated into Preferred Layers with filter button
            # Constraint layers functionality removed - using excluded/preferred layers instead

            # Connect spatial filter (formerly excluded) layers buttons
            self.dlg.btn_add_excluded_layer.clicked.connect(self.add_excluded_layer_row)
            self.dlg.btn_subtract_excluded_layers.clicked.connect(self.subtract_all_excluded_layers)

            # Setup excluded layers layout
            self.configure_excluded_layers_layout()
            # Add a default empty row if none exist yet
            if not self.excluded_layer_rows:
                self.add_excluded_layer_row()

            # Connect preferred/include layers buttons (legacy tab kept for compatibility)
            btn_add_preferred = getattr(self.dlg, 'btn_add_preferred_layer', None)
            if btn_add_preferred is not None:
                btn_add_preferred.clicked.connect(self.add_preferred_layer_row)
            btn_apply_preferred = getattr(self.dlg, 'btn_apply_preferred_layers', None)
            if btn_apply_preferred is not None:
                btn_apply_preferred.clicked.connect(self.apply_all_preferred_layers)
            
            # Setup preferred layers layout
            self.configure_preferred_layers_layout()
            # Add a default empty row if none exist yet
            if not self.preferred_layer_rows:
                self.add_preferred_layer_row()

            # Connect Decision Making tab buttons
            # Use lambda so the slot is called with no args; otherwise Qt passes clicked(bool) and we'd get from_file_layer=False
            self.dlg.btn_add_layer_to_table.clicked.connect(lambda: self.add_layer_to_weights_table())
            btn_add_from_file = getattr(self.dlg, 'btn_add_layer_from_file', None)
            if btn_add_from_file is None and hasattr(self.dlg, 'tab_6'):
                from qgis.PyQt.QtWidgets import QPushButton
                btn_add_from_file = QPushButton(self.tr("Add from file..."), self.dlg.tab_6)
                btn_add_from_file.setObjectName("btn_add_layer_from_file")
                btn_add_from_file.setGeometry(540, 10, 111, 23)
                btn_add_from_file.clicked.connect(self.add_layer_from_file_to_weights_table)
                self.dlg.btn_add_layer_from_file = btn_add_from_file
            elif btn_add_from_file is not None:
                btn_add_from_file.clicked.connect(self.add_layer_from_file_to_weights_table)
            self.dlg.btn_remove_layer_from_table.clicked.connect(self.remove_layer_from_weights_table)
            self.dlg.btn_normalize_weights.clicked.connect(self.normalize_weights)
            self.dlg.btn_validate_criteria.clicked.connect(self.validate_criteria)
            if hasattr(self.dlg, 'btnBrowseSlopeDem'):
                self.dlg.btnBrowseSlopeDem.clicked.connect(self.browse_slope_dem)
            if hasattr(self.dlg, 'btnAddSlopeCriterion'):
                self.dlg.btnAddSlopeCriterion.clicked.connect(self.add_slope_criterion)
            
            # Setup weights table
            self.setup_weights_table()
            # Connect cell change event for validation
            self.dlg.tbl_weights.cellChanged.connect(self.validate_weight_cell)

            # Connect tab change event (e.g. reset MCA progress, pre-fill slope DEM)
            tab_widget = getattr(self.dlg, 'tabWidget_EXC', None) or getattr(self.dlg, 'tabWidget', None)
            if tab_widget:
                # Hide the legacy \"Included Layers\" tab from the main UI while keeping it
                # available for any existing logic that still references its widgets.
                legacy_include_tab = getattr(self.dlg, 'tab_5', None)
                if legacy_include_tab:
                    try:
                        index = tab_widget.indexOf(legacy_include_tab)
                        if index != -1:
                            tab_widget.removeTab(index)
                    except Exception:
                        pass

                tab_widget.currentChanged.connect(self.on_tab_changed)

            # Connect MCA Evaluation buttons
            self.dlg.btn_generate_grid.clicked.connect(self.generate_mca_grid)
            self.dlg.btn_run_mca.clicked.connect(self.run_mca_calculation)
            self.dlg.btn_save_results.clicked.connect(self.save_mca_results)
            
            # Grid Value Extraction Method: Mean value (recommended) / Cell centroid
            combo_grid_method = getattr(self.dlg, 'combo_grid_value_method', None)
            if combo_grid_method is not None and isinstance(combo_grid_method, QComboBox):
                combo_grid_method.clear()
                combo_grid_method.addItem(self.tr("Mean value (recommended)"), "mean")
                combo_grid_method.addItem(self.tr("Cell centroid"), "centroid")
                combo_grid_method.setCurrentIndex(0)
                self.grid_sampling_method = "mean"
                def _on_grid_method_changed(idx):
                    val = combo_grid_method.itemData(idx)
                    if isinstance(val, str):
                        self.grid_sampling_method = val
                    elif val is not None and hasattr(val, 'value') and callable(getattr(val, 'value', None)):
                        self.grid_sampling_method = str(val.value()) if val.value() else "mean"
                    else:
                        self.grid_sampling_method = "mean" if idx == 0 else "centroid"
                combo_grid_method.currentIndexChanged.connect(_on_grid_method_changed)
            else:
                # Combo not in UI (e.g. old version); self.grid_sampling_method stays "mean"
                pass
            
            # Initialize MCA progress bar to 0 (UI file has default value of 24)
            self.update_mca_progress(0, 100)
        
        self.add_basemap()
        self.dlg.show()

    # Constraint layers functions removed - using excluded/preferred layers instead

    def configure_excluded_layers_layout(self):
        """Ensure the excluded layers layout has consistent spacing and scrolling behaviour."""
        layout = getattr(self.dlg, 'layout_excluded_layers', None)
        if not layout or not isinstance(layout, QVBoxLayout):
            return

        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(10)
        # Use proper enum access for Qt alignment
        try:
            if hasattr(Qt, 'AlignmentFlag'):
                layout.setAlignment(Qt.AlignmentFlag.AlignTop)
            else:
                layout.setAlignment(Qt.AlignTop)
        except (AttributeError, TypeError):
            layout.setAlignment(0x0020)  # AlignTop = 0x0020

        scroll_area = getattr(self.dlg, 'scrollArea_excluded_layers', None)
        if scroll_area:
            try:
                scroll_area.setWidgetResizable(True)
            except Exception:
                pass

        if self._excluded_layout_spacer is None:
            # Use proper enum access for QSizePolicy
            try:
                if hasattr(QSizePolicy, 'Policy'):
                    # PyQt6 style
                    self._excluded_layout_spacer = QSpacerItem(20, 20, QSizePolicy.Policy.Minimum, QSizePolicy.Policy.Expanding)
                else:
                    # PyQt5 style or fallback - use numeric values to avoid enum issues
                    self._excluded_layout_spacer = QSpacerItem(20, 20, 1, 7)  # Minimum=1, Expanding=7
            except (AttributeError, TypeError):
                # Fallback to numeric values: Minimum=1, Expanding=7
                self._excluded_layout_spacer = QSpacerItem(20, 20, 1, 7)
            layout.addItem(self._excluded_layout_spacer)

    def _apply_spatial_filter_row_role_style(self, row_widget, role_text):
        """Set row background color by role: Include = light green (#EAF6EA), Exclude = light red (#FDECEC)."""
        if not row_widget:
            return
        role = (role_text or "").strip()
        if role.lower() == "include":
            bg = "#EAF6EA"
        else:
            bg = "#FDECEC"
        row_widget.setStyleSheet(
            "QFrame { border: 1px solid #dcdcdc; border-radius: 4px; background-color: %s; }" % bg
        )

    def add_excluded_layer_row(self, prefill=None):
        """
        Dynamically add a new excluded layer row to the excluded layers layout.
        Each row contains:
          - QLineEdit to display the selected file path (read-only)
          - Browse button to select the file
          - QDoubleSpinBox to set the buffer distance
          - Remove button to delete the row
        """
        if not hasattr(self.dlg, 'layout_excluded_layers'):
            print("Warning: layout_excluded_layers not available on dialog")
            return

        layout = self.dlg.layout_excluded_layers
        if not isinstance(layout, QVBoxLayout):
            print("Warning: layout_excluded_layers is not a QVBoxLayout")
            return

        self.configure_excluded_layers_layout()

        row_widget = QFrame(self.dlg)
        row_widget.setObjectName(f"excluded_layer_row_{len(self.excluded_layer_rows) + 1}")
        # Use proper enum access for frame shape and shadow
        # The method expects QFrame.Shape enum, not integer
        try:
            # Try PyQt6/Qt6 style: QFrame.Shape.StyledPanel
            if hasattr(QFrame, 'Shape'):
                row_widget.setFrameShape(QFrame.Shape.StyledPanel)
                row_widget.setFrameShadow(QFrame.Shadow.Raised)
            # Try PyQt5 style: QFrame.StyledPanel (direct attribute)
            elif hasattr(QFrame, 'StyledPanel'):
                row_widget.setFrameShape(QFrame.StyledPanel)
                row_widget.setFrameShadow(QFrame.Raised)
            else:
                # Last resort: construct enum from value
                Shape = QFrame.Shape
                Shadow = QFrame.Shadow
                row_widget.setFrameShape(Shape(1))  # StyledPanel = 1
                row_widget.setFrameShadow(Shadow(0x0020))  # Raised = 0x0020
        except (AttributeError, TypeError):
            # If enum access fails completely, skip these properties
            # The frame will still function, just without the styled border
            pass
        # Role-based row background (soft pastels): Include = light green, Exclude = light red
        self._apply_spatial_filter_row_role_style(row_widget, "Exclude")
        row_widget.setMinimumHeight(70)
        # Use proper enum access for QSizePolicy
        try:
            if hasattr(QSizePolicy, 'Policy'):
                # PyQt6 style
                row_widget.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
            else:
                # PyQt5 style or fallback
                row_widget.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        except (AttributeError, TypeError):
            # Fallback to numeric values: Expanding=7, Fixed=0
            row_widget.setSizePolicy(7, 0)

        row_layout = QHBoxLayout(row_widget)
        row_layout.setContentsMargins(12, 8, 12, 8)
        row_layout.setSpacing(12)

        line_edit = QLineEdit(row_widget)
        line_edit.setPlaceholderText("Select excluded layer...")
        line_edit.setReadOnly(True)
        line_edit.setMinimumWidth(220)
        # Use proper enum access for QSizePolicy
        try:
            if hasattr(QSizePolicy, 'Policy'):
                # PyQt6 style
                line_edit.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
            else:
                # PyQt5 style or fallback
                line_edit.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        except (AttributeError, TypeError):
            # Fallback to numeric values: Expanding=7, Fixed=0
            line_edit.setSizePolicy(7, 0)

        browse_button = QPushButton("Browse", row_widget)
        browse_button.setToolTip("Select layer file")
        browse_button.setFixedWidth(70)

        filter_button = QPushButton("⚙️ Filter", row_widget)
        filter_button.setToolTip("Configure attribute filter for this layer")
        filter_button.setFixedWidth(80)
        filter_button.setEnabled(False)  # Initially disabled

        buffer_spin = QDoubleSpinBox(row_widget)
        buffer_spin.setDecimals(2)
        buffer_spin.setSuffix(" m")
        buffer_spin.setRange(0.0, 1000000.0)
        buffer_spin.setSingleStep(50.0)
        buffer_spin.setToolTip("Buffer distance in meters")
        buffer_spin.setMinimumWidth(90)

        buffer_label = QLabel("Buffer (m):", row_widget)
        # Use proper enum access for Qt alignment
        try:
            if hasattr(Qt, 'AlignmentFlag'):
                buffer_label.setAlignment(Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignRight)
            else:
                buffer_label.setAlignment(Qt.AlignVCenter | Qt.AlignRight)
        except (AttributeError, TypeError):
            buffer_label.setAlignment(0x0080 | 0x0002)  # AlignVCenter=0x0080, AlignRight=0x0002
        # Use proper enum access for QSizePolicy
        try:
            if hasattr(QSizePolicy, 'Policy'):
                buffer_label.setSizePolicy(QSizePolicy.Policy.Minimum, QSizePolicy.Policy.Preferred)
            else:
                buffer_label.setSizePolicy(QSizePolicy.Minimum, QSizePolicy.Preferred)
        except (AttributeError, TypeError):
            buffer_label.setSizePolicy(1, 4)  # Minimum=1, Preferred=4

        # Role selector (Exclude / Include) so we can use a unified spatial filter list
        role_label = QLabel("Role:", row_widget)
        try:
            if hasattr(Qt, 'AlignmentFlag'):
                role_label.setAlignment(Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignRight)
            else:
                role_label.setAlignment(Qt.AlignVCenter | Qt.AlignRight)
        except Exception:
            role_label.setAlignment(0x0080 | 0x0002)

        role_combo = QComboBox(row_widget)
        role_combo.addItems(["Exclude", "Include"])
        role_combo.setCurrentText("Exclude")
        role_combo.setToolTip("Spatial filter role for this layer")

        subtract_button = QPushButton("Subtract", row_widget)
        subtract_button.setToolTip("Subtract this layer from the prospect polygon")
        subtract_button.setFixedWidth(90)

        remove_button = QPushButton("Remove", row_widget)
        remove_button.setToolTip("Remove this excluded layer")
        remove_button.setFixedWidth(80)

        row_layout.addWidget(line_edit)
        row_layout.addWidget(browse_button)
        row_layout.addWidget(filter_button)
        row_layout.addSpacing(6)
        row_layout.addWidget(buffer_label)
        row_layout.addWidget(buffer_spin)
        row_layout.addWidget(role_label)
        row_layout.addWidget(role_combo)
        # Use proper enum access for QSizePolicy
        try:
            if hasattr(QSizePolicy, 'Policy'):
                # PyQt6 style
                row_layout.addSpacerItem(QSpacerItem(20, 0, QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Minimum))
            else:
                # PyQt5 style or fallback - use numeric values to avoid enum issues
                row_layout.addSpacerItem(QSpacerItem(20, 0, 7, 1))  # Expanding=7, Minimum=1
        except (AttributeError, TypeError):
            # Fallback to numeric values: Expanding=7, Minimum=1
            row_layout.addSpacerItem(QSpacerItem(20, 0, 7, 1))
        row_layout.addWidget(subtract_button)
        row_layout.addWidget(remove_button)
        row_layout.setStretch(0, 1)

        insert_index = layout.count()
        if self._excluded_layout_spacer is not None:
            insert_index = max(0, insert_index - 1)
        layout.insertWidget(insert_index, row_widget)

        row_info = {
            'widget': row_widget,
            'line_edit': line_edit,
            'browse_button': browse_button,
            'filter_button': filter_button,
            'buffer_spin': buffer_spin,
            'role_widget': role_combo,
            'role': "Exclude",
            'subtract_button': subtract_button,
            'remove_button': remove_button,
            'path': '',
            'filter_expression': None,
            'prepared_cache': None,
            'map_layer_ids': []
        }

        if prefill:
            path = prefill.get('path', '')
            buffer = prefill.get('buffer', 0.0)
            if path:
                row_info['path'] = path
                line_edit.setText(path)
            buffer_spin.setValue(buffer)
        else:
            buffer_spin.setValue(0.0)

        browse_button.clicked.connect(lambda _, info=row_info: self.browse_excluded_layer_file(info))
        filter_button.clicked.connect(lambda _, info=row_info: self.open_filter_dialog(info))
        subtract_button.clicked.connect(lambda _, info=row_info: self.subtract_single_excluded_layer(info))
        remove_button.clicked.connect(lambda _, info=row_info: self.remove_excluded_layer_row(info))
        buffer_spin.valueChanged.connect(lambda _, info=row_info: self.clear_excluded_layer_cache(info))

        # Keep role in sync with combo box and update row background color
        def _on_role_changed(text, info=row_info):
            info['role'] = text
            w = info.get('widget')
            if w:
                self._apply_spatial_filter_row_role_style(w, text)

        role_combo.currentTextChanged.connect(_on_role_changed)

        # Register in legacy and unified lists
        self.excluded_layer_rows.append(row_info)
        self.spatial_filter_rows.append(row_info)

        return row_info

    @staticmethod
    def _vector_layer_uri(path):
        """
        Return a URI suitable for QgsVectorLayer. For GeoPackage (single or multiple layers),
        use explicit layername when possible to avoid QGIS crash on load.
        """
        if not path or not os.path.isfile(path):
            return path
        if not path.lower().endswith('.gpkg'):
            return path
        try:
            layer = QgsVectorLayer(path, "TempGPKG", "ogr")
            if not layer.isValid():
                return path
            subs = layer.dataProvider().subLayers()
            if not subs:
                return path
            first = subs[0]
            name = first.split('!!::!!')[1] if '!!::!!' in first else first.strip()
            if name:
                return f"{path}|layername={name}"
        except Exception:
            pass
        return path

    def browse_excluded_layer_file(self, row_info):
        """Open a file dialog to select an excluded layer file and update the row.
        Supported: GeoPackage (.gpkg), Shapefile (.shp), GeoJSON (.geojson/.json), KML/KMZ, GeoTIFF (.tif) for raster.
        """
        filename, _ = QFileDialog.getOpenFileName(
            self.dlg,
            "Select Excluded Layer",
            "",
            "GeoJSON Files (*.geojson *.json);;Shapefiles (*.shp);;GeoPackage (*.gpkg);;KML/KMZ (*.kml *.kmz);;Vector Files (*.shp *.gpkg *.geojson *.json *.kml *.kmz);;Raster Files (*.tif *.tiff *.geotiff);;All Files (*)"
        )

        if filename:
            row_info['path'] = filename
            line_edit = row_info.get('line_edit')
            if line_edit:
                line_edit.setText(filename)

            filter_button = row_info.get('filter_button')
            if filter_button:
                # Problem 2: do not try to open rasters as vectors just to test validity.
                # For rasters, filters are not applicable – disable the button quietly.
                if self._is_raster_path(filename):
                    filter_button.setEnabled(False)
                else:
                    uri = self._vector_layer_uri(filename)
                    test_layer = QgsVectorLayer(uri, "Test", "ogr")
                    filter_button.setEnabled(test_layer.isValid())

            self.clear_excluded_layer_cache(row_info)

    def remove_excluded_layer_row(self, row_info):
        """Remove a specific excluded layer row from the layout and internal tracking."""
        row_widget = row_info.get('widget')
        if not row_widget or not hasattr(self.dlg, 'layout_excluded_layers'):
            return

        layout = self.dlg.layout_excluded_layers
        if not isinstance(layout, QVBoxLayout):
            return

        index = layout.indexOf(row_widget)
        if index != -1:
            item = layout.takeAt(index)
            if item:
                widget = item.widget()
                if widget:
                    widget.deleteLater()

        # Remove from internal lists
        self.excluded_layer_rows = [info for info in self.excluded_layer_rows if info is not row_info]
        self.spatial_filter_rows = [info for info in self.spatial_filter_rows if info is not row_info]
        self.remove_excluded_layer_map_layers(row_info)

    def get_excluded_row_display_name(self, row_info):
        """Get a friendly name for an excluded layer row."""
        try:
            index = self.excluded_layer_rows.index(row_info) + 1
        except ValueError:
            index = len(self.excluded_layer_rows) + 1
        return f"Excluded Layer {index}"

    def remove_excluded_layer_map_layers(self, row_info):
        """Remove any map layers associated with a specific excluded layer row."""
        layer_ids = row_info.get('map_layer_ids', [])
        if not layer_ids:
            return

        project = QgsProject.instance()
        for layer_id in layer_ids:
            project.removeMapLayer(layer_id)

        row_info['map_layer_ids'] = []

    def clear_excluded_layer_cache(self, row_info):
        """Clear cached preparation results for an excluded layer row."""
        row_info['prepared_cache'] = None
        self.remove_excluded_layer_map_layers(row_info)

    def ensure_excluded_layer_visible(self, row_info, vector_path, suffix="Processed"):
        """Add the prepared excluded layer to the map if it's not already visible."""
        project = QgsProject.instance()
        existing_ids = [
            layer_id for layer_id in row_info.get('map_layer_ids', [])
            if project.mapLayer(layer_id)
        ]
        if existing_ids:
            row_info['map_layer_ids'] = existing_ids
            return

        layer_name = f"{self.get_excluded_row_display_name(row_info)} ({suffix})"
        layer = QgsVectorLayer(vector_path, layer_name, "ogr")
        if layer.isValid():
            project.addMapLayer(layer)
            row_info.setdefault('map_layer_ids', []).append(layer.id())

    def invalidate_all_excluded_layer_caches(self):
        """Clear cached preparation data for all spatial filter rows (exclude/include) when AOI changes."""
        seen = set()
        for row_info in (
            list(self.excluded_layer_rows)
            + list(self.preferred_layer_rows)
            + list(getattr(self, "spatial_filter_rows", []) or [])
        ):
            rid = id(row_info)
            if rid in seen:
                continue
            seen.add(rid)
            row_info["prepared_cache"] = None
            self.remove_excluded_layer_map_layers(row_info)

    # ---------- Raster-based spatial filter helpers (replaces slow polygon difference/intersection) ----------

    def _normalize_path(self, path):
        """Normalize path to forward slashes so GDAL receives consistent paths (avoids Windows mixed-separator errors)."""
        if not path:
            return path
        return str(path).replace("\\", "/")

    def _ref_info_from_layer(self, raster_layer):
        """
        Build reference grid info from a QgsRasterLayer (no file re-open).
        Returns dict: extent, width, height, crs, res_x, res_y; or None if invalid.
        """
        if not raster_layer or not raster_layer.isValid():
            return None
        extent = raster_layer.extent()
        if extent.isEmpty():
            return None
        return {
            'extent': extent,
            'width': raster_layer.width(),
            'height': raster_layer.height(),
            'crs': raster_layer.crs(),
            'res_x': raster_layer.rasterUnitsPerPixelX(),
            'res_y': raster_layer.rasterUnitsPerPixelY(),
        }

    def get_prospect_raster_layer_from_ui(self, require_prospect_result=False):
        """
        Get the prospect raster for spatial filtering.
        If require_prospect_result=True (used by spatial filter): ONLY use prospect_result_path
        so the grid is always from the Prospect Area output (prospect_area.tif). No fallback to line edit.
        Otherwise: prefer prospect_result_path, then line edit. Returns (layer, normalized_path) or (None, None).
        """
        path = None
        if self.prospect_result_path and os.path.exists(self.prospect_result_path):
            path = self.prospect_result_path.strip()
        if not require_prospect_result and not path and getattr(self.dlg, 'lineEditProspectPath', None):
            path = (self.dlg.lineEditProspectPath.text() or '').strip()
        if not path or not os.path.exists(path):
            return None, None
        path = self._normalize_path(path)
        # Prefer existing layer in project that matches this path (same file)
        for layer in QgsProject.instance().mapLayers().values():
            if not isinstance(layer, QgsRasterLayer) or not layer.isValid():
                continue
            src = self._normalize_path(layer.source())
            if src == path:
                return layer, path
            try:
                if os.path.exists(src) and os.path.exists(path) and os.path.samefile(src, path):
                    return layer, path
            except Exception:
                pass
        layer = QgsRasterLayer(path, "Prospect", "gdal")
        if not layer.isValid():
            return None, None
        return layer, path

    def _get_reference_raster_info(self, reference_raster_path):
        """
        Get extent, size, CRS and resolution from a reference raster.
        Returns dict with keys: extent (QgsRectangle), width, height, crs, res_x, res_y, or None if invalid.
        """
        if not reference_raster_path or not os.path.exists(reference_raster_path):
            return None
        path = self._raster_path_for_gdal(reference_raster_path)
        ref = QgsRasterLayer(path, "Reference")
        if not ref.isValid():
            return None
        extent = ref.extent()
        if extent.isEmpty():
            return None
        w = ref.width()
        h = ref.height()
        crs = ref.crs()
        res_x = ref.rasterUnitsPerPixelX()
        res_y = ref.rasterUnitsPerPixelY()
        gt = None
        extent_from_gt = extent
        try:
            provider_gt = ref.dataProvider().geoTransform()
            if provider_gt and len(provider_gt) >= 6:
                gt = tuple(float(v) for v in provider_gt[:6])
                xmin = float(gt[0])
                ymax = float(gt[3])
                xmax = xmin + float(w) * float(gt[1])
                ymin = ymax + float(h) * float(gt[5])
                extent_from_gt = QgsRectangle(xmin, ymin, xmax, ymax)
                res_x = float(gt[1])
                res_y = float(abs(gt[5]))
        except Exception:
            pass
        if _GDAL_AVAILABLE:
            try:
                ds = gdal.Open(path, gdal.GA_ReadOnly)
                if ds:
                    gt = ds.GetGeoTransform()
                    if gt:
                        w = int(ds.RasterXSize)
                        h = int(ds.RasterYSize)
                        xmin = float(gt[0])
                        ymax = float(gt[3])
                        xmax = xmin + float(w) * float(gt[1])
                        ymin = ymax + float(h) * float(gt[5])
                        extent_from_gt = QgsRectangle(xmin, ymin, xmax, ymax)
                        res_x = float(gt[1])
                        res_y = float(abs(gt[5]))
                ds = None
            except Exception:
                gt = None
        return {
            # Always use extent derived from master geotransform when available.
            'extent': extent_from_gt,
            'extent_from_gt': extent_from_gt,
            'width': w,
            'height': h,
            'crs': crs,
            'res_x': res_x,
            'res_y': res_y,
            'geotransform': gt,
        }

    def _geotransform_from_master_gdal(self, raster_path):
        """Read geotransform only from the raster file via GDAL (master grid for -tr / checks)."""
        if not _GDAL_AVAILABLE or not raster_path or not os.path.exists(raster_path):
            return None
        try:
            p = self._raster_path_for_gdal(raster_path)
            ds = gdal.Open(p, gdal.GA_ReadOnly)
            if not ds:
                return None
            gt = ds.GetGeoTransform()
            ds = None
            if not gt or len(gt) < 6:
                return None
            return tuple(float(gt[i]) for i in range(6))
        except Exception:
            return None

    def _master_tr_te_bounds_from_gdal(self, raster_path):
        """
        Single GDAL read of master: -tr and -te bounds matching exact raster dimensions.
        Use with gdalwarp EXTRA (no -tap; -tap without fixed -te changes output size vs master).
        """
        if not _GDAL_AVAILABLE or not raster_path or not os.path.exists(raster_path):
            return None
        try:
            p = self._raster_path_for_gdal(raster_path)
            ds = gdal.Open(p, gdal.GA_ReadOnly)
            if not ds:
                return None
            gt = ds.GetGeoTransform()
            w = int(ds.RasterXSize)
            h = int(ds.RasterYSize)
            ds = None
            if not gt or len(gt) < 6 or w <= 0 or h <= 0:
                return None
            tr_x = float(gt[1])
            tr_y = float(abs(gt[5]))
            xmin = float(gt[0])
            ymax = float(gt[3])
            xmax = xmin + float(w) * float(gt[1])
            ymin = ymax + float(h) * float(gt[5])
            return {
                "tr_x": tr_x,
                "tr_y": tr_y,
                "xmin": xmin,
                "ymin": ymin,
                "xmax": xmax,
                "ymax": ymax,
                "w": w,
                "h": h,
            }
        except Exception:
            return None

    def _strict_validate_raster_matches_master(self, output_raster_path, master_raster_path):
        """
        Strict post-create validation:
        output MUST exactly match master in width/height/CRS/geotransform.
        Raises RuntimeError on any mismatch.
        """
        out_path = self._normalize_path(output_raster_path)
        master_path = self._normalize_path(master_raster_path)
        if not out_path or not os.path.exists(out_path):
            raise RuntimeError(f"Output raster missing: {out_path}")
        if not master_path or not os.path.exists(master_path):
            raise RuntimeError(f"Master raster missing: {master_path}")

        out_layer = QgsRasterLayer(out_path, "StrictOut", "gdal")
        ref_layer = QgsRasterLayer(master_path, "StrictMaster", "gdal")
        if not out_layer.isValid() or not ref_layer.isValid():
            raise RuntimeError("Strict validation failed: invalid raster layer(s).")

        if out_layer.width() != ref_layer.width() or out_layer.height() != ref_layer.height():
            raise RuntimeError(
                "Strict grid mismatch (size): output {}x{} vs master {}x{}.".format(
                    out_layer.width(), out_layer.height(), ref_layer.width(), ref_layer.height()
                )
            )
        if out_layer.crs().authid() != ref_layer.crs().authid():
            raise RuntimeError(
                "Strict grid mismatch (CRS): output {} vs master {}.".format(
                    out_layer.crs().authid(), ref_layer.crs().authid()
                )
            )
        if not _GDAL_AVAILABLE:
            raise RuntimeError("Strict grid validation requires GDAL geotransform support.")

        ds_ref = gdal.Open(self._raster_path_for_gdal(master_path), gdal.GA_ReadOnly)
        ds_out = gdal.Open(self._raster_path_for_gdal(out_path), gdal.GA_ReadOnly)
        if not ds_ref or not ds_out:
            raise RuntimeError("Strict grid validation failed: cannot open raster(s) with GDAL.")
        gt_ref = ds_ref.GetGeoTransform()
        gt_out = ds_out.GetGeoTransform()
        ds_ref = None
        ds_out = None
        if not gt_ref or not gt_out:
            raise RuntimeError("Strict grid validation failed: missing geotransform.")
        _gt_atol = 1e-9
        for i in range(6):
            if abs(float(gt_out[i]) - float(gt_ref[i])) > _gt_atol:
                raise RuntimeError(
                    "Strict grid mismatch (geotransform): output {} vs master {}.".format(
                        gt_out, gt_ref
                    )
                )
        return True

    def get_master_grid(self, reference_raster_path):
        """
        Strict master-grid helper.
        Single source of truth for extent/resolution/CRS/origin/size from a reference raster file.
        """
        return self._get_reference_raster_info(reference_raster_path)

    def _require_wind_master_path(self):
        """Return normalized wind master path or raise RuntimeError."""
        wind_master_path = getattr(self, "wind_master_path", None)
        if not wind_master_path or not os.path.exists(wind_master_path):
            raise RuntimeError("Wind master raster is missing. Run Wind Clip first.")
        return self._normalize_path(wind_master_path)

    def _get_wind_master_or_fail(self):
        """Hard-fail accessor for the single wind master grid."""
        if not hasattr(self, "wind_master_path") or not self.wind_master_path:
            raise RuntimeError("Wind master path invalid or missing.")
        p = self._normalize_path(self.wind_master_path)
        if not p or not os.path.exists(p):
            raise RuntimeError("Wind master path invalid or missing.")
        return p

    def align_to_master(self, input_raster_path, reference_raster_path, output_path, nodata_value=MCA_NODATA):
        """
        Align any raster EXACTLY to the master grid defined by reference_raster_path.
        """
        return self._warp_raster_to_reference_grid(
            reference_raster_path,
            input_raster_path,
            output_path,
            nodata_value=nodata_value,
            use_reference_as_grid=True
        )

    def _ensure_aligned_to_master_before_calc(self, input_raster_path, label, nodata_value=MCA_NODATA):
        """
        Ensure raster is aligned to wind master BEFORE any raster calculation/masking.
        Returns path guaranteed to match master grid.
        """
        src = self._normalize_path(input_raster_path)
        master = self._get_wind_master_or_fail()
        if not src or not os.path.exists(src):
            raise RuntimeError(f"{label}: input raster missing")
        if self._rasters_have_identical_grid(src, master):
            QgsMessageLog.logMessage(
                f"[DEBUG] {label}: already aligned to master grid.",
                "WindSuitability",
                Qgis.Info,
            )
            return src
        aligned_path = self._normalize_path(
            os.path.join(self.get_plugin_temp_dir(), f"{label}_master_{uuid.uuid4().hex[:8]}.tif")
        )
        self._release_and_remove_path(aligned_path)
        if not self._warp_raster_to_reference_grid(master, src, aligned_path, nodata_value=nodata_value):
            raise RuntimeError(f"{label}: failed to align to master grid before calc")
        self._strict_validate_raster_matches_master(aligned_path, master)
        QgsMessageLog.logMessage(
            f"[DEBUG] {label}: aligned to master grid for calc.",
            "WindSuitability",
            Qgis.Info,
        )
        return aligned_path

    def _get_clipped_wind_master_path(self):
        """
        Clipped wind raster is the preferred master grid for the full workflow.
        """
        candidates = []
        p_master = getattr(self, "wind_master_path", None)
        if p_master:
            candidates.append(p_master)
        p0 = getattr(self, "wind_result_path", None)
        if p0:
            candidates.append(p0)
        try:
            if hasattr(self.dlg, "lineEditWindPath"):
                p1 = (self.dlg.lineEditWindPath.text() or "").strip()
                if p1:
                    candidates.append(p1)
        except Exception:
            pass
        for p in candidates:
            pn = self._normalize_path(p)
            if pn and os.path.exists(pn):
                lyr = QgsRasterLayer(pn, "WindMaster", "gdal")
                if lyr.isValid() and lyr.width() > 0 and lyr.height() > 0:
                    return pn
        return None

    def get_master_reference_raster_for_decision_making(self):
        """
        Get the master reference raster for Decision Making / MCA criterion rasterization.
        Decision Making must NOT depend on the MCA grid (which is created later). Instead use:
        - Preferred: spatial_filtered.tif (same dir as prospect output)
        - Fallback: prospect_area.tif = prospect_result_path
        Returns (QgsRasterLayer or None, path or None, source_name str for logging).
        """
        # STRICT priority: clipped wind raster is master grid for all MCA raster work.
        wind_master = self._get_clipped_wind_master_path()
        if wind_master and os.path.exists(wind_master):
            layer = QgsRasterLayer(wind_master, "MasterGrid", "gdal")
            if layer.isValid() and layer.width() > 0 and layer.height() > 0:
                return layer, wind_master, "Clipped_Wind_Master"

        prospect_path = getattr(self, 'prospect_result_path', None)
        if not prospect_path or not os.path.exists(prospect_path):
            return None, None, None
        prospect_dir = os.path.dirname(prospect_path)
        prospect_dir = self._normalize_path(prospect_dir) if prospect_dir else None
        if not prospect_dir:
            return None, None, None
        # Preferred: spatial_filtered.tif
        spatial_filtered_path = self._normalize_path(os.path.join(prospect_dir, self.SPATIAL_FILTERED_TIF))
        if os.path.exists(spatial_filtered_path):
            layer = QgsRasterLayer(spatial_filtered_path, "MasterGrid", "gdal")
            if layer.isValid() and layer.width() > 0 and layer.height() > 0:
                return layer, spatial_filtered_path, self.SPATIAL_FILTERED_TIF
        # Fallback: prospect_area.tif
        pa_path = self._normalize_path(prospect_path)
        if os.path.exists(pa_path):
            layer = QgsRasterLayer(pa_path, "MasterGrid", "gdal")
            if layer.isValid() and layer.width() > 0 and layer.height() > 0:
                return layer, pa_path, "Prospect_Area"
        return None, None, None

    def _rasterize_vector_to_reference_grid(self, vector_path, reference_raster_path, output_raster_path, burn_value=1.0, layer_name=None, ref_info=None):
        """
        Rasterize a vector layer to the exact grid of the reference raster (same extent, size, CRS).
        Burns burn_value (default 1) where vector exists, 0 elsewhere. Returns True on success.
        If ref_info dict is provided, use it instead of opening reference_raster_path (avoids re-open).
        """
        info = ref_info if ref_info else self._get_reference_raster_info(reference_raster_path)
        if not info:
            return False
        crs = info['crs']
        if not vector_path or not os.path.exists(vector_path):
            return False
        out_path = self._normalize_path(output_raster_path)
        vec = QgsVectorLayer(vector_path, "ToRaster", "ogr")
        if not vec.isValid():
            return False
        if not crs or not crs.isValid():
            return False
        rasterize_input_path = self._normalize_path(vector_path)
        reproj_temp = None
        try:
            # Hard guard: vector must be in the exact analysis/reference CRS before rasterization.
            # This prevents accidental rasterization in EPSG:4326 and guarantees grid alignment.
            vec_crs = vec.crs()
            if not vec_crs.isValid():
                return False
            if vec_crs.authid() != crs.authid():
                reproj_temp = self._normalize_path(
                    os.path.join(tempfile.gettempdir(), f"rasterize_reproj_{uuid.uuid4().hex[:8]}.gpkg")
                )
                processing.run("native:reprojectlayer", {
                    "INPUT": vec,
                    "TARGET_CRS": crs.authid(),
                    "OUTPUT": reproj_temp,
                })
                if not os.path.exists(reproj_temp):
                    return False
                reproj_layer = QgsVectorLayer(reproj_temp, "ToRasterReprojected", "ogr")
                if not reproj_layer.isValid() or not reproj_layer.crs().isValid() or reproj_layer.crs().authid() != crs.authid():
                    return False
                rasterize_input_path = reproj_temp

            # Single-step rasterize to the exact reference grid (size+extent+CRS).
            # Avoids a second warp pass that can add runtime and edge drift.
            res_x = float(abs(info.get("res_x", 0.0)))
            res_y = float(abs(info.get("res_y", 0.0)))
            if res_x <= 0 or res_y <= 0:
                return False
            out_tmp = self._normalize_path(
                os.path.join(self.get_plugin_temp_dir(), "rasterize_raw_{}.tif".format(uuid.uuid4().hex[:8]))
            )
            self._release_and_remove_path(out_tmp)
            QgsMessageLog.logMessage(
                "[WindSuitability] [rasterize-debug] vector rasterize -tr=({}, {}) ref_grid={}x{}".format(
                    res_x, res_y, info.get("width"), info.get("height")
                ),
                "WindSuitability",
                Qgis.Info,
            )
            try:
                # Same rule as MCA / exclude rasterization: default GDAL behavior (no -at).
                # ALL_TOUCHED would expand AOI edges vs other masks and vs the analysis grid.
                extra_args = f'-a_srs {crs.authid()}'
                processing.run("gdal:rasterize", {
                    'INPUT': rasterize_input_path,
                    'FIELD': '',
                    'BURN': float(burn_value),
                    'UNITS': 0,
                    'NODATA': 0.0,
                    'OPTIONS': '',
                    'DATA_TYPE': 0,
                    'INIT': 0.0,
                    'INVERT': False,
                    'WIDTH': int(info.get("width", 0)) if info else 0,
                    'HEIGHT': int(info.get("height", 0)) if info else 0,
                    'EXTENT': info.get("extent_from_gt", info.get("extent")) if info else None,
                    'EXTRA': extra_args,
                    'OUTPUT': out_tmp,
                })
            except Exception:
                return False
            if not os.path.exists(out_tmp):
                return False
            try:
                _tl = QgsRasterLayer(out_tmp, "RastDbg", "gdal")
                if _tl.isValid():
                    QgsMessageLog.logMessage(
                        "[WindSuitability] [rasterize-debug] raw rasterize output size={}x{}".format(
                            _tl.width(), _tl.height()
                        ),
                        "WindSuitability",
                        Qgis.Info,
                    )
            except Exception:
                pass
            self._release_and_remove_path(out_path)
            try:
                shutil.move(out_tmp, out_path)
            except Exception:
                try:
                    shutil.copy2(out_tmp, out_path)
                except Exception:
                    pass
            try:
                if os.path.exists(out_tmp):
                    os.remove(out_tmp)
            except Exception:
                pass
            success = os.path.exists(out_path)
            if success:
                try:
                    self._strict_validate_raster_matches_master(out_path, reference_raster_path)
                except Exception:
                    return False
            if self.DEBUG_SPATIAL:
                name = layer_name or (os.path.splitext(os.path.basename(vector_path))[0] if vector_path else "vector")
                QgsMessageLog.logMessage("[SpatialFilter] Rasterizing layer: {}".format(name), "WindSuitability", Qgis.Info)
            return success
        except Exception as e:
            return False
        finally:
            if reproj_temp and os.path.exists(reproj_temp):
                try:
                    os.remove(reproj_temp)
                except Exception:
                    pass

    def _warp_raster_to_reference_grid(self, reference_raster_path, input_path, output_path, nodata_value=MCA_NODATA, use_reference_as_grid=False):
        """
        Warp a raster to match the reference raster's grid (extent, resolution, CRS).
        Uses nearest-neighbor resampling. Returns True on success.
        Contract: exactly one definitive warp pass per output (no fallback re-warp).

        use_reference_as_grid: When True, align to the given reference_raster_path's grid exactly
        (no wind-master override). Used after gdal:rasterize so masks match prospect/other rasters
        pixel-for-pixel. Grid (-tr, -te, dimensions) is cloned from the reference raster via GDAL only.
        """
        QgsMessageLog.logMessage(
            "[TRACE] ENTERED _warp_raster_to_reference_grid",
            "WindSuitability",
            Qgis.Info,
        )
        grid_ref = self._normalize_path(reference_raster_path)

        if not grid_ref or not os.path.exists(grid_ref):
            raise RuntimeError("Invalid reference raster path.")

        ref_info = self._get_reference_raster_info(grid_ref)
        if not ref_info or not input_path or not os.path.exists(input_path):
            raise RuntimeError("Invalid raster alignment inputs or missing reference raster info.")
        crs = ref_info['crs']
        if not crs or not crs.isValid():
            raise RuntimeError("Invalid CRS on reference raster.")
        try:
            if not _GDAL_AVAILABLE:
                raise RuntimeError("GDAL is required for raster alignment.")
            ref_gdal_path = self._raster_path_for_gdal(grid_ref)
            ds = gdal.Open(ref_gdal_path, gdal.GA_ReadOnly)
            if ds is None:
                raise RuntimeError("Cannot open reference raster")
            gt = ds.GetGeoTransform()
            proj = ds.GetProjection()
            cols = ds.RasterXSize
            rows = ds.RasterYSize
            ds = None
            xmin = gt[0]
            ymax = gt[3]
            xmax = xmin + cols * gt[1]
            ymin = ymax + rows * gt[5]
            tr_x = abs(gt[1])
            tr_y = abs(gt[5])
            w_ref = cols
            h_ref = rows
            QgsMessageLog.logMessage(
                "[WindSuitability] [align-debug] reference GDAL clone -tr=({}, {}) size={}x{} -te from GT".format(
                    tr_x, tr_y, w_ref, h_ref
                ),
                "WindSuitability",
                Qgis.Info,
            )

            # Inspect input pixel size for diagnostics only; never used for warp.
            input_px_x = None
            input_px_y = None
            try:
                in_layer = QgsRasterLayer(self._raster_path_for_gdal(input_path), "AlignInput", "gdal")
                if in_layer.isValid():
                    input_px_x = float(abs(in_layer.rasterUnitsPerPixelX()))
                    input_px_y = float(abs(in_layer.rasterUnitsPerPixelY()))
            except Exception:
                pass

            tol = 1e-12
            if input_px_x is not None and input_px_y is not None:
                if abs(tr_x - input_px_x) < tol and abs(tr_y - input_px_y) < tol:
                    QgsMessageLog.logMessage(
                        "[WindSuitability] Alignment guard: input pixel size ~= master pixel size; forcing master GT -tr anyway.",
                        "WindSuitability",
                        Qgis.Info,
                    )
                else:
                    QgsMessageLog.logMessage(
                        "[WindSuitability] Alignment guard: input pixel size differs from master; overriding with master GT -tr.",
                        "WindSuitability",
                        Qgis.Info,
                    )

            QgsMessageLog.logMessage(
                "[WindSuitability] Warp EXTRA: -tr {} {} -te {} {} {} {}".format(
                    tr_x, tr_y, xmin, ymin, xmax, ymax
                ),
                "WindSuitability",
                Qgis.Info,
            )
            processing.run("gdal:warpreproject", {
                'INPUT': input_path,
                'SOURCE_CRS': None,
                'TARGET_CRS': crs.authid(),
                'RESAMPLING': 0,
                'NODATA': nodata_value,
                'TARGET_RESOLUTION': None,
                'TARGET_EXTENT': None,
                'EXTRA': f'-tr {tr_x} {tr_y} -te {xmin} {ymin} {xmax} {ymax}',
                'OUTPUT': output_path
            })
            if os.path.exists(output_path):
                try:
                    _chk = QgsRasterLayer(output_path, "AlignDbg", "gdal")
                    if _chk.isValid():
                        QgsMessageLog.logMessage(
                            "[WindSuitability] [align-debug] output size={}x{} (master GDAL {}x{})".format(
                                _chk.width(), _chk.height(), w_ref, h_ref
                            ),
                            "WindSuitability",
                            Qgis.Info,
                        )
                except Exception:
                    pass
                # Hard-stop on any grid mismatch.
                self._strict_validate_raster_matches_master(output_path, grid_ref)
                out_layer = QgsRasterLayer(output_path, "AlignCheck", "gdal")
                if out_layer.isValid():
                    # Hard contract: aligned raster must exactly match reference dimensions.
                    if out_layer.width() == w_ref and out_layer.height() == h_ref:
                        # Hard contract: geotransform/origin must also match the reference grid.
                        if _GDAL_AVAILABLE:
                            try:
                                ds_ref = gdal.Open(self._raster_path_for_gdal(grid_ref), gdal.GA_ReadOnly)
                                ds_out = gdal.Open(output_path, gdal.GA_ReadOnly)
                                if ds_ref and ds_out:
                                    gt_ref = ds_ref.GetGeoTransform()
                                    gt_out = ds_out.GetGeoTransform()
                                    ds_ref = None
                                    ds_out = None
                                    same_gt = True
                                    if not gt_ref or not gt_out:
                                        same_gt = False
                                    else:
                                        for i in range(6):
                                            if not np.isclose(float(gt_ref[i]), float(gt_out[i]), rtol=0.0, atol=1e-9):
                                                same_gt = False
                                                break
                                    if not same_gt:
                                        QgsMessageLog.logMessage(
                                            "[WindSuitability] Alignment geotransform/origin mismatch with reference grid.",
                                            "WindSuitability",
                                            Qgis.Warning,
                                        )
                                        raise RuntimeError("Alignment geotransform/origin mismatch with reference grid.")
                            except Exception:
                                raise
                        QgsMessageLog.logMessage("[WindSuitability] Raster aligned to target grid.", "WindSuitability", Qgis.Info)
                        return True
                    got_w = int(out_layer.width())
                    got_h = int(out_layer.height())
                    exp_w = w_ref
                    exp_h = h_ref
                    QgsMessageLog.logMessage(
                        "[WindSuitability] Alignment dimension mismatch (got {}x{}, expected {}x{}).".format(
                            got_w, got_h, exp_w, exp_h
                        ),
                        "WindSuitability",
                        Qgis.Warning,
                    )
            raise RuntimeError("Alignment output missing or invalid after warp.")
        except Exception as e:
            QgsMessageLog.logMessage(f"[ERROR] {str(e)}", "WindSuitability", Qgis.Critical)
            raise

    def _set_raster_nodata(self, raster_path, nodata_value=MCA_NODATA):
        """
        Force a consistent NoData value on output rasters.
        Returns True when band metadata is updated (or already set), False on failure.
        """
        if not _GDAL_AVAILABLE or not raster_path or not os.path.exists(raster_path):
            return False
        try:
            ds = gdal.Open(self._normalize_path(raster_path), gdal.GA_Update)
            if not ds:
                return False
            band = ds.GetRasterBand(1)
            if not band:
                ds = None
                return False
            band.SetNoDataValue(float(nodata_value))
            band.FlushCache()
            ds.FlushCache()
            ds = None
            return True
        except Exception:
            return False

    def _rasters_have_identical_grid(self, raster_a_path, raster_b_path):
        """
        Check CRS/size/extent and geotransform equality for pixel-perfect raster math.
        """
        a = QgsRasterLayer(raster_a_path, "grid_a", "gdal")
        b = QgsRasterLayer(raster_b_path, "grid_b", "gdal")
        if not a.isValid() or not b.isValid():
            return False
        if a.width() != b.width() or a.height() != b.height():
            return False
        if a.crs().authid() != b.crs().authid():
            return False
        ea = a.extent()
        eb = b.extent()
        if (
            not np.isclose(ea.xMinimum(), eb.xMinimum(), rtol=0.0, atol=1e-9)
            or not np.isclose(ea.xMaximum(), eb.xMaximum(), rtol=0.0, atol=1e-9)
            or not np.isclose(ea.yMinimum(), eb.yMinimum(), rtol=0.0, atol=1e-9)
            or not np.isclose(ea.yMaximum(), eb.yMaximum(), rtol=0.0, atol=1e-9)
        ):
            return False
        if _GDAL_AVAILABLE:
            try:
                dsa = gdal.Open(self._normalize_path(raster_a_path), gdal.GA_ReadOnly)
                dsb = gdal.Open(self._normalize_path(raster_b_path), gdal.GA_ReadOnly)
                if not dsa or not dsb:
                    return False
                gta = dsa.GetGeoTransform()
                gtb = dsb.GetGeoTransform()
                dsa = None
                dsb = None
                if not gta or not gtb:
                    return False
                for i in range(6):
                    if not np.isclose(float(gta[i]), float(gtb[i]), rtol=0.0, atol=1e-9):
                        return False
            except Exception:
                return False
        return True

    def _exclude_raster_layer_to_prospect_mask(self, raster_path, prospect_path, ref_info, output_mask_path):
        """
        Excluded layer is a raster: warp once to the prospect (A) grid and build byte mask B.
        No raster→polygon→raster. Geotransform and dimensions come from prospect_path only.
        Output: 1 = excluded cell, 0 = not excluded. Pixels NoData or zero in warped source → 0.
        """
        if not _GDAL_AVAILABLE or not _NUMPY_AVAILABLE:
            return False
        rp = self._normalize_path(self._raster_path_for_gdal(raster_path))
        pp = self._normalize_path(prospect_path)
        out_path = self._normalize_path(output_mask_path)
        if not rp or not os.path.exists(rp) or not pp or not os.path.exists(pp):
            return False
        self._release_and_remove_path(out_path)
        tmp_warped = self._normalize_path(
            os.path.join(tempfile.gettempdir(), f"excl_raster_warp_{uuid.uuid4().hex[:8]}.tif")
        )
        self._release_and_remove_path(tmp_warped)
        src_layer = QgsRasterLayer(rp, "excl_src", "gdal")
        warp_nd = MCA_NODATA
        if src_layer.isValid():
            try:
                v = src_layer.dataProvider().sourceNoDataValue(1)
                if v is not None and np.isfinite(float(v)):
                    warp_nd = float(v)
            except Exception:
                pass
        wind_master = self._require_wind_master_path()
        if not self._warp_raster_to_reference_grid(wind_master, rp, tmp_warped, nodata_value=warp_nd):
            try:
                if os.path.exists(tmp_warped):
                    os.remove(tmp_warped)
            except Exception:
                pass
            return False
        try:
            ds = gdal.Open(tmp_warped, gdal.GA_ReadOnly)
            ref_ds = gdal.Open(wind_master, gdal.GA_ReadOnly)
            if not ds or not ref_ds:
                return False
            if ds.RasterXSize != ref_ds.RasterXSize or ds.RasterYSize != ref_ds.RasterYSize:
                return False
            band = ds.GetRasterBand(1)
            arr = np.asarray(band.ReadAsArray(), dtype=np.float64)
            ndv = band.GetNoDataValue()
            gt = ref_ds.GetGeoTransform()
            proj = ref_ds.GetProjection()
            ds, ref_ds = None, None
            valid = np.isfinite(arr)
            if ndv is not None:
                ndv_f = float(ndv)
                if np.isnan(ndv_f):
                    valid = valid & ~np.isnan(arr)
                else:
                    valid = valid & ~np.isclose(arr, ndv_f, rtol=0.0, atol=1e-8)
            # Excluded where source has a valid, non-zero value (thematic / binary exclude rasters)
            mask = np.where(valid & (np.nan_to_num(arr) != 0.0), np.uint8(1), np.uint8(0))
            driver = gdal.GetDriverByName("GTiff")
            if not driver:
                return False
            h, w = mask.shape[0], mask.shape[1]
            ds_out = driver.Create(out_path, w, h, 1, gdal.GDT_Byte, ["COMPRESS=LZW", "TILED=YES"])
            if not ds_out:
                return False
            ds_out.SetGeoTransform(gt)
            ds_out.SetProjection(proj)
            b_out = ds_out.GetRasterBand(1)
            b_out.SetNoDataValue(0)
            b_out.WriteArray(mask)
            b_out.FlushCache()
            ds_out.FlushCache()
            ds_out = None
            QgsMessageLog.logMessage(
                "[WindSuitability] Exclude raster → prospect mask (no polygonize): {}".format(out_path),
                "WindSuitability",
                Qgis.Info,
            )
            return os.path.exists(out_path)
        except Exception:
            return False
        finally:
            try:
                if os.path.exists(tmp_warped):
                    os.remove(tmp_warped)
            except Exception:
                pass

    def _create_zero_byte_raster_same_grid(self, reference_raster_path, output_raster_path, ref_info=None):
        """Byte raster, same dimensions/CRS/geotransform as reference, all pixels 0. No rectangular vector layer."""
        if not _GDAL_AVAILABLE or not _NUMPY_AVAILABLE:
            return False
        info = ref_info if ref_info else self._get_reference_raster_info(reference_raster_path)
        if not info:
            return False
        out_path = self._normalize_path(output_raster_path)
        self._release_and_remove_path(out_path)
        ref_path = self._normalize_path(reference_raster_path)
        try:
            ds = gdal.Open(ref_path, gdal.GA_ReadOnly)
            if not ds:
                return False
            w, h = ds.RasterXSize, ds.RasterYSize
            gt = ds.GetGeoTransform()
            proj = ds.GetProjection()
            ds = None
            out = np.zeros((h, w), dtype=np.uint8)
            driver = gdal.GetDriverByName("GTiff")
            if not driver:
                return False
            ds_out = driver.Create(out_path, w, h, 1, gdal.GDT_Byte, ["COMPRESS=LZW", "TILED=YES"])
            if not ds_out:
                return False
            ds_out.SetGeoTransform(gt)
            ds_out.SetProjection(proj)
            band = ds_out.GetRasterBand(1)
            band.SetNoDataValue(0)
            band.WriteArray(out)
            band.FlushCache()
            ds_out.FlushCache()
            ds_out = None
            return os.path.exists(out_path)
        except Exception:
            return False

    def _user_aoi_vector_path_in_crs(self, target_crs):
        """Save user AOI to a temp GPKG in target_crs for gdal:rasterize. Returns path or None."""
        ul = self.get_user_aoi_layer()
        if not ul or not ul.isValid() or ul.featureCount() == 0:
            return None
        if not target_crs or not target_crs.isValid():
            return None
        temp_path = self._normalize_path(
            os.path.join(tempfile.gettempdir(), "aoi_poly_mask_{}.gpkg".format(uuid.uuid4().hex[:8]))
        )
        try:
            if ul.crs().isValid() and ul.crs().authid() == target_crs.authid():
                processing.run("native:savefeatures", {"INPUT": ul, "OUTPUT": temp_path})
            else:
                processing.run("native:reprojectlayer", {
                    "INPUT": ul,
                    "TARGET_CRS": target_crs.authid(),
                    "OUTPUT": temp_path,
                })
            return temp_path if os.path.exists(temp_path) else None
        except Exception:
            return None

    def _reference_raster_overlaps_user_aoi(self, ref_layer):
        """
        True if ref_layer's extent intersects the user AOI extent transformed to ref CRS.
        If there is no valid user AOI, returns True (no constraint).
        """
        ul = self.get_user_aoi_layer()
        if not ul or not ul.isValid() or ul.featureCount() == 0:
            return True
        if not ref_layer or not ref_layer.isValid():
            return True
        try:
            tr = QgsCoordinateTransform(ul.crs(), ref_layer.crs(), QgsProject.instance())
            aoi_bb = tr.transformBoundingBox(ul.extent())
            return aoi_bb.intersects(ref_layer.extent())
        except Exception as ex:
            QgsMessageLog.logMessage(
                "[WindSuitability] AOI vs reference overlap check failed: {}".format(ex),
                "WindSuitability",
                Qgis.Warning,
            )
            return True

    def _rasterize_user_aoi_binary_mask(self, reference_raster_path, output_raster_path, ref_info=None):
        """
        Rasterize the user AOI polygon to the reference grid: 1 inside polygon, 0 outside.
        Replaces full-extent constant '1' masks (no const_rect / artificial rectangle AOI).
        """
        info = ref_info if ref_info else self._get_reference_raster_info(reference_raster_path)
        if not info:
            return False
        vpath = self._user_aoi_vector_path_in_crs(info["crs"])
        if not vpath:
            return False
        try:
            ok = self._rasterize_vector_to_reference_grid(
                vpath,
                reference_raster_path,
                output_raster_path,
                1.0,
                layer_name="AOI_MASK",
                ref_info=info,
            )
            return ok
        finally:
            try:
                if os.path.exists(vpath):
                    os.remove(vpath)
            except Exception:
                pass

    def _raster_multiply_byte_rasters(self, path_a, path_b, output_path):
        """Element-wise multiply two byte rasters (same grid). Output = A * B clipped to [0,1]."""
        if not _GDAL_AVAILABLE or not _NUMPY_AVAILABLE:
            return False
        out_path = self._normalize_path(output_path)
        self._release_and_remove_path(out_path)
        pa, pb = self._normalize_path(path_a), self._normalize_path(path_b)
        try:
            dsa = gdal.Open(pa, gdal.GA_ReadOnly)
            dsb = gdal.Open(pb, gdal.GA_ReadOnly)
            if not dsa or not dsb:
                return False
            if dsa.RasterXSize != dsb.RasterXSize or dsa.RasterYSize != dsb.RasterYSize:
                return False
            A = np.asarray(dsa.GetRasterBand(1).ReadAsArray(), dtype=np.float64)
            B = np.asarray(dsb.GetRasterBand(1).ReadAsArray(), dtype=np.float64)
            gt = dsa.GetGeoTransform()
            proj = dsa.GetProjection()
            dsa, dsb = None, None
            out = np.clip(A * B, 0, 1).astype(np.uint8)
            driver = gdal.GetDriverByName("GTiff")
            if not driver:
                return False
            ds_out = driver.Create(out_path, out.shape[1], out.shape[0], 1, gdal.GDT_Byte, ["COMPRESS=LZW", "TILED=YES"])
            if not ds_out:
                return False
            ds_out.SetGeoTransform(gt)
            ds_out.SetProjection(proj)
            band = ds_out.GetRasterBand(1)
            band.SetNoDataValue(0)
            band.WriteArray(out)
            band.FlushCache()
            ds_out.FlushCache()
            ds_out = None
            return os.path.exists(out_path)
        except Exception:
            return False

    def _apply_user_aoi_mask_to_byte_raster_on_own_grid(self, byte_raster_path):
        """
        Multiply a byte suitability raster by the user AOI polygon mask on the SAME grid as byte_raster_path.
        All -tr/-te for the mask come from _get_reference_raster_info(byte_raster_path) only.

        Root cause addressed: wind×depth prospect lives on a rectangular grid; clip/threshold can leave 1s
        in bbox corners outside the true AOI polygon. This zeros those pixels before polygonize/export.
        No-op if there is no user AOI layer.
        """
        if not self.get_user_aoi_layer():
            return True
        if not _GDAL_AVAILABLE or not _NUMPY_AVAILABLE:
            return False
        bp = self._normalize_path(byte_raster_path)
        if not bp or not os.path.exists(bp):
            return False
        try:
            self.ensure_output_dirs(bp)
        except Exception:
            pass
        ref_info = self._get_reference_raster_info(bp)
        if not ref_info:
            return False
        try:
            ref_layer = QgsRasterLayer(bp, "ProspectMaskRef", "gdal")
            if ref_layer.isValid() and not self._reference_raster_overlaps_user_aoi(ref_layer):
                QgsMessageLog.logMessage(
                    "[WindSuitability] AOI does not overlap prospect raster extent.",
                    "WindSuitability",
                    Qgis.Warning,
                )
                return False
        except Exception:
            pass
        mask_path = self._normalize_path(
            os.path.join(self.get_plugin_temp_dir(), "prospect_aoi_mask_{}.tif".format(uuid.uuid4().hex[:8]))
        )
        self._release_and_remove_path(mask_path)
        if not self._rasterize_user_aoi_binary_mask(bp, mask_path, ref_info=ref_info):
            QgsMessageLog.logMessage(
                "[WindSuitability] Failed to rasterize AOI mask on prospect grid.",
                "WindSuitability",
                Qgis.Warning,
            )
            return False
        try:
            _min, _max, nz, total = self._log_mask_stats("ProspectAOIMask", mask_path)
            if total > 0 and nz == 0:
                QgsMessageLog.logMessage(
                    "[WindSuitability] AOI mask has zero non-zero pixels on prospect grid.",
                    "WindSuitability",
                    Qgis.Warning,
                )
                return False
        except Exception:
            pass
        tmp_out = self._normalize_path(bp + ".aoi_masked.tmp.tif")
        self._release_and_remove_path(tmp_out)
        ok = self._raster_multiply_byte_rasters(bp, mask_path, tmp_out)
        try:
            if os.path.exists(mask_path):
                os.remove(mask_path)
        except Exception:
            pass
        if not ok:
            try:
                if os.path.exists(tmp_out):
                    os.remove(tmp_out)
            except Exception:
                pass
            return False
        try:
            # Replace in one step; do not pre-delete target to avoid lock-related false failures.
            os.replace(tmp_out, bp)
        except Exception:
            try:
                shutil.copy2(tmp_out, bp)
                os.remove(tmp_out)
            except Exception:
                QgsMessageLog.logMessage(
                    "[WindSuitability] Failed to write AOI-masked prospect raster back to original path.",
                    "WindSuitability",
                    Qgis.Warning,
                )
                return False
        return os.path.exists(bp)

    def _multiply_float_raster_by_aoi_mask(self, float_raster_path, reference_raster_path, output_path, ref_info=None):
        """
        Multiply a float suitability raster by the user AOI binary mask on the same grid.
        Pixels outside the AOI polygon are set to MCA_NODATA. If there is no user AOI, copies input to output when paths differ.
        """
        if not _GDAL_AVAILABLE or not _NUMPY_AVAILABLE:
            return False
        ul = self.get_user_aoi_layer()
        out_path = self._normalize_path(output_path)
        self._release_and_remove_path(out_path)
        fp = self._normalize_path(float_raster_path)
        rp = self._normalize_path(reference_raster_path)
        if not fp or not os.path.exists(fp):
            return False
        if not ul or not ul.isValid() or ul.featureCount() == 0:
            if os.path.normpath(fp) != os.path.normpath(out_path):
                try:
                    shutil.copy2(fp, out_path)
                    return os.path.exists(out_path)
                except Exception:
                    return False
            return True
        if not rp or not os.path.exists(rp):
            return False
        mask_path = os.path.join(tempfile.gettempdir(), "aoi_float_mask_{}.tif".format(uuid.uuid4().hex[:8]))
        try:
            info = ref_info if ref_info else self._get_reference_raster_info(rp)
            if not info:
                return False
            if not self._rasterize_user_aoi_binary_mask(rp, mask_path, ref_info=info):
                return False
            dsa = gdal.Open(fp, gdal.GA_ReadOnly)
            dsm = gdal.Open(self._normalize_path(mask_path), gdal.GA_ReadOnly)
            if not dsa or not dsm:
                return False
            if dsa.RasterXSize != dsm.RasterXSize or dsa.RasterYSize != dsm.RasterYSize:
                return False
            A = np.asarray(dsa.GetRasterBand(1).ReadAsArray(), dtype=np.float64)
            M = np.asarray(dsm.GetRasterBand(1).ReadAsArray(), dtype=np.float64)
            gt = dsa.GetGeoTransform()
            proj = dsa.GetProjection()
            dsa, dsm = None, None
            out = np.where(M > 0, A, MCA_NODATA).astype(np.float32)
            driver = gdal.GetDriverByName("GTiff")
            if not driver:
                return False
            ds_out = driver.Create(out_path, out.shape[1], out.shape[0], 1, gdal.GDT_Float32, ["COMPRESS=LZW", "TILED=YES"])
            if not ds_out:
                return False
            ds_out.SetGeoTransform(gt)
            ds_out.SetProjection(proj)
            band = ds_out.GetRasterBand(1)
            band.SetNoDataValue(MCA_NODATA)
            band.WriteArray(out)
            band.FlushCache()
            ds_out.FlushCache()
            ds_out = None
            return os.path.exists(out_path)
        except Exception:
            return False
        finally:
            try:
                if os.path.exists(mask_path):
                    os.remove(mask_path)
            except Exception:
                pass

    def _create_constant_raster(self, reference_raster_path, output_raster_path, constant_value, ref_info=None):
        """
        Deprecated for spatial filters: constant 1 over full extent is wrong — use _rasterize_user_aoi_binary_mask.
        Only constant 0 is supported here (all-zero byte grid, no rectangle vector).
        """
        if float(constant_value) != 0.0:
            QgsMessageLog.logMessage(
                "[WindSuitability] _create_constant_raster(non-zero) is deprecated; use AOI polygon mask.",
                "WindSuitability",
                Qgis.Warning,
            )
            return False
        return self._create_zero_byte_raster_same_grid(reference_raster_path, output_raster_path, ref_info=ref_info)

    def _log_mask_stats(self, label, raster_path):
        """
        Returns (min_value, max_value, non_zero_count, total_pixels) for a mask raster.
        On error returns (0, 0, 0, 0). Used for validation and debug logging.
        """
        try:
            if not raster_path or not os.path.exists(raster_path):
                return 0, 0, 0, 0
            layer = QgsRasterLayer(raster_path, label, "gdal")
            if not layer.isValid():
                return 0, 0, 0, 0
            provider = layer.dataProvider()
            stats = provider.bandStatistics(1, QgsRasterBandStats.All, layer.extent(), 0)
            min_val = stats.minimumValue
            max_val = stats.maximumValue
            width = layer.width()
            height = layer.height()
            total = width * height
            block = provider.block(1, layer.extent(), width, height)
            if not block:
                return min_val, max_val, 0, total
            non_zero = 0
            no_data = block.noDataValue()
            for y in range(height):
                for x in range(width):
                    v = block.value(y, x)
                    if v == no_data:
                        continue
                    if v != 0:
                        non_zero += 1
            return min_val, max_val, non_zero, total
        except Exception:
            return 0, 0, 0, 0

    def _fix_and_clip_vector_to_aoi(self, vector_path, aoi_polygon_layer, label="layer"):
        """
        Run native:fixgeometries then native:clip to AOI polygon. Returns path to clipped result or None.
        Ensures vectors are valid and strictly clipped to prospect AOI before rasterization.
        """
        if not vector_path or not os.path.exists(vector_path) or not aoi_polygon_layer or not aoi_polygon_layer.isValid():
            return None
        temp_dir = self.get_plugin_temp_dir()
        fixed_path = self._normalize_path(os.path.join(temp_dir, "spatial_fixed_{}_{}.gpkg".format(label, uuid.uuid4().hex[:8])))
        clipped_path = self._normalize_path(os.path.join(temp_dir, "spatial_clipped_{}_{}.gpkg".format(label, uuid.uuid4().hex[:8])))
        try:
            processing.run("native:fixgeometries", {
                'INPUT': self._normalize_path(vector_path),
                'OUTPUT': fixed_path
            })
            if not os.path.exists(fixed_path):
                return None
            processing.run("native:clip", {
                'INPUT': fixed_path,
                'OVERLAY': aoi_polygon_layer,
                'OUTPUT': clipped_path
            })
            if os.path.exists(clipped_path):
                return clipped_path
        except Exception:
            pass
        return None

    def _multipart_to_single_parts(self, vector_path, label="single"):
        """
        Run native:multiparttosingleparts to convert MultiPolygon (and other multipart) features to single parts.
        Returns path to output layer or None on failure. Ensures each polygon part is rasterized.
        """
        if not vector_path or not os.path.exists(vector_path):
            return None
        temp_dir = self.get_plugin_temp_dir()
        out_path = self._normalize_path(os.path.join(temp_dir, "spatial_singleparts_{}_{}.gpkg".format(label, uuid.uuid4().hex[:8])))
        try:
            processing.run("native:multiparttosingleparts", {
                'INPUT': self._normalize_path(vector_path),
                'OUTPUT': out_path
            })
            if os.path.exists(out_path):
                return out_path
        except Exception:
            pass
        return None

    def _reproject_vector_to_crs(self, vector_path, target_crs, label="reproj"):
        """
        Reproject vector layer to target_crs. Returns path to output or None.
        Ensures vector coordinates match the raster CRS before rasterization.
        """
        if not vector_path or not os.path.exists(vector_path) or not target_crs or not target_crs.isValid():
            return None
        vl = QgsVectorLayer(vector_path, "Check", "ogr")
        if not vl.isValid():
            return None
        if vl.crs().isValid() and vl.crs().authid() == target_crs.authid():
            return vector_path  # already in target CRS
        temp_dir = self.get_plugin_temp_dir()
        out_path = self._normalize_path(os.path.join(temp_dir, "spatial_{}_{}.gpkg".format(label, uuid.uuid4().hex[:8])))
        try:
            processing.run("native:reprojectlayer", {
                'INPUT': self._normalize_path(vector_path),
                'TARGET_CRS': target_crs.authid(),
                'OUTPUT': out_path
            })
            if os.path.exists(out_path):
                return out_path
        except Exception:
            pass
        return None

    def _vector_extent_intersects_raster_extent(self, vector_layer, raster_extent, raster_crs):
        """Return True if the vector layer extent intersects the raster extent (in raster CRS)."""
        if not vector_layer or not vector_layer.isValid() or raster_extent.isEmpty():
            return False
        try:
            vec_crs = vector_layer.crs()
            if not vec_crs.isValid() or not raster_crs.isValid():
                return True
            if vec_crs != raster_crs:
                transform = QgsCoordinateTransform(vec_crs, raster_crs, QgsProject.instance())
                vec_ext = vector_layer.extent()
                vec_ext = transform.transformBoundingBox(vec_ext)
            else:
                vec_ext = vector_layer.extent()
            return vec_ext.intersects(raster_extent)
        except Exception:
            return True
