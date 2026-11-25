-- Prove2me | solution 1 for ReciprocityTheory.Cheb.norm_Gs_add_sub_le_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:06:07.684185+00:00
-- url     : https://prove2.me/submissions/face5a35-428f-4fae-a4d0-5d28ccabda55

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
import Theorems.Thm_ReciprocityTheory_Cheb_half_le_normAtPlace_add
import Theorems.Thm_ReciprocityTheory_Cheb_normAtPlace_add_pos
import Theorems.Thm_ReciprocityTheory_Cheb_abs_log_norm_sub_le
import Theorems.Thm_ReciprocityTheory_Cheb_norm_logMap_sub_le
import Theorems.Thm_ReciprocityTheory_Cheb_rsgn_add
import Theorems.Thm_ReciprocityTheory_Cheb_abs_uphi_sub_le
import Theorems.Thm_ReciprocityTheory_Cheb_Gs_eq_real
import Theorems.Thm_ReciprocityTheory_Cheb_abs_rpow_neg_sub_le
import Theorems.Thm_ReciprocityTheory_Cheb_rpow_neg_le_inv
import Theorems.Thm_ReciprocityTheory_Cheb_pow_le_norm_of_le
import Theorems.Thm_ReciprocityTheory_Cheb_uphi_le_one
import Theorems.Thm_ReciprocityTheory_Cheb_uphi_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {l : ℕ} (χ : DirichletCharacter ℂ l) {s : ℝ} (hs : s ∈ Set.Icc (1 : ℝ) 2)
    {A : ℝ} (hA : 0 ≤ A)
    (hAb : ∀ x y : mixedSpace E, ∑ i, |ucoord x i - ucoord y i| ≤ A * ‖logMap x - logMap y‖)
    {y k : mixedSpace E} {B a : ℝ} (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a) (ha2 : 2 ≤ a)
    (hy : ∀ w, a ≤ normAtPlace w y) :
    ‖Gs χ s (y + k) - Gs χ s y‖ ≤
      (A * (4 * (2 * B / a)) + 2 * ((Module.finrank ℚ E : ℝ) * (2 * B / a))) *
        ((a / 2) ^ Module.finrank ℚ E)⁻¹ := by
  have ha0 : 0 < a := by linarith
  have hyw : ∀ w, 0 < normAtPlace w y := fun w => lt_of_lt_of_le ha0 (hy w)
  have hyN : mixedEmbedding.norm y ≠ 0 := mixedEmbedding.norm_ne_zero_iff.mpr fun w => (hyw w).ne'
  have hykN : mixedEmbedding.norm (y + k) ≠ 0 :=
    mixedEmbedding.norm_ne_zero_iff.mpr fun w => (normAtPlace_add_pos hB hk ha hy w).ne'
  set m := (a / 2) ^ Module.finrank ℚ E with hm_def
  have hm1 : 1 ≤ m := one_le_pow₀ (by linarith)
  have hmN : m ≤ mixedEmbedding.norm y :=
    pow_le_norm_of_le (by linarith) fun w => by linarith [hy w]
  have hmN' : m ≤ mixedEmbedding.norm (y + k) :=
    pow_le_norm_of_le (by linarith) fun w => by
      linarith [hy w, half_le_normAtPlace_add hk ha hy w]
  have hδ : 0 ≤ 2 * B / a := div_nonneg (by linarith) ha0.le

  have hu : |uphi (y + k) - uphi y| ≤ A * (4 * (2 * B / a)) :=
    (abs_uphi_sub_le hykN hyN).trans ((hAb _ _).trans
      (mul_le_mul_of_nonneg_left (norm_logMap_sub_le hB hk ha hy) hA))

  have hP : |mixedEmbedding.norm (y + k) ^ (-s) - mixedEmbedding.norm y ^ (-s)| ≤
      2 * ((Module.finrank ℚ E : ℝ) * (2 * B / a)) * m⁻¹ := by
    refine (abs_rpow_neg_sub_le hs.1 hm1 hmN hmN').trans ?_
    have hl := abs_log_norm_sub_le hB hk ha hy
    have hm0 : 0 ≤ m⁻¹ := inv_nonneg.mpr (by linarith)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hs.2 hl (abs_nonneg _) (by norm_num)) hm0
  have hP' : mixedEmbedding.norm (y + k) ^ (-s) ≤ m⁻¹ := rpow_neg_le_inv hs.1 hm1 hmN'
  have hP0 : 0 ≤ mixedEmbedding.norm (y + k) ^ (-s) :=
    Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _
  have hu0 : 0 ≤ uphi y := uphi_nonneg y
  have hu1 : uphi y ≤ 1 := uphi_le_one y
  have hreal : |uphi (y + k) * mixedEmbedding.norm (y + k) ^ (-s) - uphi y * mixedEmbedding.norm y ^ (-s)| ≤
      (A * (4 * (2 * B / a)) + 2 * ((Module.finrank ℚ E : ℝ) * (2 * B / a))) * m⁻¹ := by
    have e : uphi (y + k) * mixedEmbedding.norm (y + k) ^ (-s) - uphi y * mixedEmbedding.norm y ^ (-s) =
        (uphi (y + k) - uphi y) * mixedEmbedding.norm (y + k) ^ (-s) +
          uphi y * (mixedEmbedding.norm (y + k) ^ (-s) - mixedEmbedding.norm y ^ (-s)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hP0, abs_of_nonneg hu0]
    have h1 : |uphi (y + k) - uphi y| * mixedEmbedding.norm (y + k) ^ (-s) ≤ A * (4 * (2 * B / a)) * m⁻¹ :=
      mul_le_mul hu hP' hP0 (by positivity)
    have h2 : uphi y * |mixedEmbedding.norm (y + k) ^ (-s) - mixedEmbedding.norm y ^ (-s)| ≤
        2 * ((Module.finrank ℚ E : ℝ) * (2 * B / a)) * m⁻¹ := by
      calc _ ≤ 1 * |mixedEmbedding.norm (y + k) ^ (-s) - mixedEmbedding.norm y ^ (-s)| :=
            mul_le_mul_of_nonneg_right hu1 (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hP
    linarith
  rw [Gs_eq_real, Gs_eq_real, rsgn_add hB hk ha hy, ← mul_sub, norm_mul, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  calc ‖χ (rsgn y : ZMod l)‖ * |_| ≤ 1 * |uphi (y + k) * mixedEmbedding.norm (y + k) ^ (-s) -
        uphi y * mixedEmbedding.norm y ^ (-s)| :=
        mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (abs_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hreal
end ReciprocityTheory.Cheb
