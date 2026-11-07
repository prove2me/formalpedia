-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap_add_opposite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:42:38.140488+00:00
-- url     : https://prove2.me/submissions/184e3182-3d45-45d9-9155-582afc72580e

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_latitude_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_univ
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_cap_opposite_union
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_cap_opposite_inter
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_measurableSet_cap


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) (c : ℝ) :
    area (cap u c) + area (cap (opposite u) (-c)) = ENNReal.ofReal (4 * Real.pi) := by
  have h := measure_union_add_inter (μ := area) (cap u c)
    (measurableSet_cap (opposite u) (-c))
  rw [cap_opposite_union,cap_opposite_inter,area_latitude_zero,add_zero,area_univ] at h
  exact h.symm
end QEC.Coding.ProbabilisticConstruction.SphericalCap
