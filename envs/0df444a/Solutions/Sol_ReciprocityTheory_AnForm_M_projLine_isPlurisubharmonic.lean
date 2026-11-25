-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.projLine_isPlurisubharmonic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:39.326419+00:00
-- url     : https://prove2.me/submissions/611d4180-e67a-46a4-9a19-9ed908af6ab1

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Theorems.Thm_ReciprocityTheory_AnForm_M_fsPot_chart
import Theorems.Thm_ReciprocityTheory_AnForm_M_hasDerivAt_fubiniStudyProfile
import Theorems.Thm_ReciprocityTheory_AnForm_M_hasDerivAt_fubiniStudyProfileInv
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_leviForm_radial
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : IsPsh p1 fsPot := by
  intro x j y hy v
  rcases fsPot_chart x j with h | ⟨h, hne⟩
  · rw [h]
    have ht : 0 ≤ ‖y 0‖ ^ 2 := by positivity
    have hG : ∀ᶠ t in 𝓝 (‖y 0‖ ^ 2), HasDerivAt fubiniStudyProfile ((1 / 2) * (1 + t)⁻¹) t :=
      (lt_mem_nhds (by linarith : (-1 : ℝ) < ‖y 0‖ ^ 2)).mono fun t ht' => hasDerivAt_fubiniStudyProfile ht'
    have hG' := (((hasDerivAt_id' (‖y 0‖ ^ 2)).const_add 1).inv
      (by positivity : (1 : ℝ) + ‖y 0‖ ^ 2 ≠ 0)).const_mul (1 / 2 : ℝ)
    rw [projLine_leviForm_radial (F := fun w => fubiniStudyProfile (fsQ w)) (Filter.Eventually.of_forall fun w => rfl) hG hG' v]
    refine mul_nonneg ?_ (by positivity)
    have h1 : (0 : ℝ) < 1 + ‖y 0‖ ^ 2 := by positivity
    beta_reduce
    generalize ‖y 0‖ ^ 2 = t at ht h1 ⊢
    have key : 1 / 2 * (-1 / (1 + t) ^ 2) * t + 1 / 2 * (1 + t)⁻¹ = 1 / (2 * (1 + t) ^ 2) := by
      field_simp
      ring
    have hpos : 0 ≤ 1 / (2 * (1 + t) ^ 2) := by positivity
    linarith [key, hpos]
  · rw [h]
    have ht : 0 < ‖y 0‖ ^ 2 := pow_pos (norm_pos_iff.2 (hne y hy)) 2
    have hG : ∀ᶠ t in 𝓝 (‖y 0‖ ^ 2), HasDerivAt fubiniStudyProfileInv (-(1 / 2) * (t * (t + 1))⁻¹) t :=
      (lt_mem_nhds ht).mono fun t ht' => hasDerivAt_fubiniStudyProfileInv ht'
    have hG' := (((hasDerivAt_id' (‖y 0‖ ^ 2)).mul ((hasDerivAt_id' (‖y 0‖ ^ 2)).add_const 1)).inv
      (by positivity : ‖y 0‖ ^ 2 * (‖y 0‖ ^ 2 + 1) ≠ 0)).const_mul (-(1 / 2) : ℝ)
    rw [projLine_leviForm_radial (F := fun w => fubiniStudyProfileInv (fsQ w)) (Filter.Eventually.of_forall fun w => rfl) hG hG' v]
    refine mul_nonneg ?_ (by positivity)
    simp only [Pi.mul_apply]
    beta_reduce
    generalize ‖y 0‖ ^ 2 = t at ht ⊢
    have ht0 : t ≠ 0 := ht.ne'
    have ht1 : t + 1 ≠ 0 := by positivity
    have hu : t * (t + 1) * (t * (t + 1))⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero ht0 ht1)
    have hpos : 0 ≤ 1 / 2 * (t * (t * (t + 1))⁻¹) ^ 2 := by positivity
    have hv : (t * (t + 1)) ^ 2 * ((t * (t + 1)) ^ 2)⁻¹ = 1 :=
      mul_inv_cancel₀ (pow_ne_zero 2 (mul_ne_zero ht0 ht1))
    refine le_of_le_of_eq hpos ?_
    linear_combination (1 / 2 * (2 * t + 1) * t * ((t * (t + 1)) ^ 2)⁻¹ *
        (1 + t * (t + 1) * (t * (t + 1))⁻¹) - 1 / 2 * (t * (t + 1))⁻¹) * hu +
      (-(1 / 2) * (2 * t + 1) * t * ((t * (t + 1))⁻¹) ^ 2) * hv
end ReciprocityTheory.AnForm.M
