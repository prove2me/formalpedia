-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.projLine_isHolomorphicSection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:33:51.797443+00:00
-- url     : https://prove2.me/submissions/15812cdc-05d0-4aad-8307-51ecfb3b3a0d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Theorems.Thm_ReciprocityTheory_AnForm_M_fsPot_U_infty
import Theorems.Thm_ReciprocityTheory_AnForm_M_fsPot_U_coe
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_fsPot___infty_ec505eb666d6
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_fsPot___coe_5dad99c71fe1
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLineSection_infty
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLineSection_coe
import Theorems.Thm_ReciprocityTheory_AnForm_M_holomorphicOn_infiniteCoord
import Theorems.Thm_ReciprocityTheory_AnForm_M_holoOn_const
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
private theorem half_log_one_add_inv_sq_sub_eq_neg_log {ζ : ℂ} (h : ζ ≠ 0) :
    (1 / 2) * Real.log (1 + ‖ζ⁻¹‖ ^ 2) - (1 / 2) * Real.log (1 + ‖ζ‖ ^ 2) = -Real.log ‖ζ‖ := by
  have hn : 0 < ‖ζ‖ := norm_pos_iff.2 h
  have hn2 : ‖ζ‖ ^ 2 ≠ 0 := by positivity
  have h1 : 1 + ‖ζ⁻¹‖ ^ 2 = (1 + ‖ζ‖ ^ 2) / ‖ζ‖ ^ 2 := by
    rw [norm_inv, inv_pow, add_div, div_self hn2, one_div, add_comm]
  rw [h1, Real.log_div (by positivity) hn2, Real.log_pow]
  push_cast
  ring
private theorem norm_inv_mul_exp_half_log_eq_of_ne_zero {ζ : ℂ} (h : ζ ≠ 0) :
    ‖ζ⁻¹‖ * Real.exp (-((1 / 2) * Real.log (1 + ‖ζ⁻¹‖ ^ 2))) =
      ‖(1 : ℂ)‖ * Real.exp (-((1 / 2) * Real.log (1 + ‖ζ‖ ^ 2))) := by
  have hn : ‖ζ‖ ≠ 0 := norm_ne_zero_iff.2 h
  have e := half_log_one_add_inv_sq_sub_eq_neg_log h
  have e2 : -((1 / 2) * Real.log (1 + ‖ζ⁻¹‖ ^ 2)) =
      -((1 / 2) * Real.log (1 + ‖ζ‖ ^ 2)) + Real.log ‖ζ‖ := by linarith
  rw [e2, Real.exp_add, Real.exp_log (norm_pos_iff.2 h), norm_inv, norm_one,
    mul_comm (Real.exp _) ‖ζ‖, ← mul_assoc, inv_mul_cancel₀ hn]
end
end ReciprocityTheory.AnForm.M
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : IsSection p1 fsPot projectiveLinePairSection := by
  refine ⟨fun x => ?_, ?_⟩
  · induction x with
    | infty =>
      rw [projLineSection_infty, fsPot_U_infty]
      exact holomorphicOn_infiniteCoord
    | coe z =>
      rw [projLineSection_coe, fsPot_U_coe]
      exact holoOn_const _ 1
  · intro x x' y hy
    induction x with
    | infty =>
      induction x' with
      | infty => rfl
      | coe z' =>
        obtain ⟨hy1, hy2⟩ := hy
        rw [fsPot_U_infty] at hy1
        rw [fsPot_U_coe] at hy2
        obtain ⟨ζ, rfl⟩ := hy2
        have hζ : ζ ≠ 0 := fun h => hy1 (by rw [h])
        rw [projLineSection_infty, projLineSection_coe, fsPot_φ_infty, fsPot_φ_coe]
        exact norm_inv_mul_exp_half_log_eq_of_ne_zero hζ
    | coe z =>
      induction x' with
      | infty =>
        obtain ⟨hy1, hy2⟩ := hy
        rw [fsPot_U_coe] at hy1
        rw [fsPot_U_infty] at hy2
        obtain ⟨ζ, rfl⟩ := hy1
        have hζ : ζ ≠ 0 := fun h => hy2 (by rw [h])
        rw [projLineSection_infty, projLineSection_coe, fsPot_φ_infty, fsPot_φ_coe]
        exact (norm_inv_mul_exp_half_log_eq_of_ne_zero hζ).symm
      | coe z'' =>
        rw [projLineSection_coe, projLineSection_coe, fsPot_φ_coe, fsPot_φ_coe]
end ReciprocityTheory.AnForm.M
