-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:41:11.283355+00:00
-- url     : https://prove2.me/submissions/805dacba-ff48-4e41-ac2a-5e1452a11687

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap_axis_invariant
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_solidCapCone_north
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap_eq_three_volume_solid
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_volume_axialCone


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    area (cap u c) = ENNReal.ofReal (2 * Real.pi * (1-c)) := by
  rw [area_cap_axis_invariant u north c, area_cap_eq_three_volume_solid,
    solidCapCone_north, volume_axialCone hc0 hc1]
  have he : (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) := by norm_num
  rw [he, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
  congr 1
  ring
end QEC.Coding.ProbabilisticConstruction.SphericalCap
