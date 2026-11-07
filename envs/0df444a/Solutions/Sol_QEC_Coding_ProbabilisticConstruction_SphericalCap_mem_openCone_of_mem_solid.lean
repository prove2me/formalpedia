-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.mem_openCone_of_mem_solid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:38:27.170506+00:00
-- url     : https://prove2.me/submissions/4431efa9-0f8d-48f6-9e66-fb43d34ee747

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) (c : ℝ) {x : Space}
    (hx : x ∈ solidCapCone u c) (h0 : x ≠ 0) (h1 : ‖x‖ ≠ 1) :
    x ∈ Ioo (0 : ℝ) 1 • ((↑) '' cap u c) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr h0
  let s : Sphere := ⟨‖x‖⁻¹ • x, by
    simp only [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']⟩
  refine ⟨‖x‖, ⟨hn, lt_of_le_of_ne hx.1 h1⟩, (s : Space), ?_, ?_⟩
  · refine ⟨s, ?_, rfl⟩
    change c ≤ inner ℝ (u : Space) (‖x‖⁻¹ • x)
    rw [real_inner_smul_right]
    have h := (div_le_div_iff_of_pos_right hn).mpr hx.2
    simpa [div_eq_mul_inv, mul_comm, mul_assoc, hn.ne'] using h
  · change ‖x‖ • (‖x‖⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
end QEC.Coding.ProbabilisticConstruction.SphericalCap
