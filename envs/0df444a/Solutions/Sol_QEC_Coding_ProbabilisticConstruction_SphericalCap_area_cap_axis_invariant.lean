-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap_axis_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:40:13.178689+00:00
-- url     : https://prove2.me/submissions/d3b7a471-d9e1-4fd4-bc82-31aa3f85b209

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_solidCapCone_reflection
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap_eq_three_volume_solid
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axisReflection_measurePreserving
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_solidCapCone_measurable


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u v : Sphere) (c : ℝ) :
    area (cap u c) = area (cap v c) := by
  rw [area_cap_eq_three_volume_solid, area_cap_eq_three_volume_solid,
    solidCapCone_reflection u v c]
  congr 1
  exact (axisReflection_measurePreserving (u : Space) (v : Space)).measure_preimage
    (solidCapCone_measurable v c).nullMeasurableSet
end QEC.Coding.ProbabilisticConstruction.SphericalCap
