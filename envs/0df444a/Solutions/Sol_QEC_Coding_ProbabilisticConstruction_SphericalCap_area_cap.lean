-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:43:30.11106+00:00
-- url     : https://prove2.me/submissions/afbb2c49-4be5-4d67-99f7-a41f5bd00008

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap_axis_invariant
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap_of_pos
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap_add_opposite
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap_ne_top


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) {c : ℝ} (hc0 : -1 < c) (hc1 : c < 1) :
    area (cap u c) = ENNReal.ofReal (2 * Real.pi * (1-c)) := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have hother := area_cap_of_pos (opposite u) (c := -c) (by linarith) (by linarith)
    have hs := area_cap_add_opposite u c
    rw [hother] at hs
    apply (ENNReal.toReal_eq_toReal_iff' (area_cap_ne_top u c) ENNReal.ofReal_ne_top).mp
    have hr := congrArg ENNReal.toReal hs
    rw [ENNReal.toReal_add (area_cap_ne_top u c) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * Real.pi),
      ENNReal.toReal_ofReal (mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) (by linarith : 0 ≤ 1 - -c))] at hr
    rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) (by linarith : 0 ≤ 1-c))]
    linarith
  · have hs := area_cap_add_opposite u 0
    rw [neg_zero,area_cap_axis_invariant (opposite u) u 0] at hs
    apply (ENNReal.toReal_eq_toReal_iff' (area_cap_ne_top u 0) ENNReal.ofReal_ne_top).mp
    have hr := congrArg ENNReal.toReal hs
    rw [ENNReal.toReal_add (area_cap_ne_top u 0) (area_cap_ne_top u 0),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * Real.pi)] at hr
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi * (1-(0:ℝ)))]
    linarith
  · exact area_cap_of_pos u hc hc1
end QEC.Coding.ProbabilisticConstruction.SphericalCap
