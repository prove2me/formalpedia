-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.capLaw_le_of_area_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:44:29.475419+00:00
-- url     : https://prove2.me/submissions/a15cb063-e25b-4e36-b79c-c076a4480718

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) {c A : ℝ} (hc0 : -1 < c) (hc1 : c < 1)
    {E : Set Sphere} (hE : MeasurableSet E) (hA : area E ≤ ENNReal.ofReal A) :
    capLaw u c E ≤ ENNReal.ofReal (A / (2 * Real.pi * (1-c))) := by
  have hd : 0 < 2 * Real.pi * (1-c) := mul_pos (by positivity) (sub_pos.mpr hc1)
  calc
    capLaw u c E = (area (cap u c))⁻¹ * area (E ∩ cap u c) := by
      rw [capLaw,Measure.smul_apply,Measure.restrict_apply hE,smul_eq_mul]
    _ ≤ (area (cap u c))⁻¹ * ENNReal.ofReal A := by
      exact mul_le_mul' le_rfl ((measure_mono inter_subset_left).trans hA)
    _ = ENNReal.ofReal (A / (2 * Real.pi * (1-c))) := by
      rw [area_cap u hc0 hc1,ENNReal.ofReal_div_of_pos hd,div_eq_mul_inv,mul_comm]
end QEC.Coding.ProbabilisticConstruction.SphericalCap
