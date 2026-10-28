-- Prove2me | solution 1 for UtilityTokens.ICOChoice.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:44:11.840091+00:00
-- url     : https://prove2.me/submissions/d394f000-e9e9-4b3c-b30c-e45e2e6b71f2

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting

namespace Aux_UT_lemma1
open UtilityTokens.ICOChoice

lemma interior_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    thetaInterior a ≤ thetaInterior b := by
  unfold thetaInterior
  have hqa : (0:ℝ) ≤ a ^ 2 + a + 1 := by nlinarith
  have hqb : (0:ℝ) ≤ b ^ 2 + b + 1 := by nlinarith
  have sa0 := Real.sqrt_nonneg (a ^ 2 + a + 1)
  have sb0 := Real.sqrt_nonneg (b ^ 2 + b + 1)
  have sa2 := Real.sq_sqrt hqa
  have sb2 := Real.sq_sqrt hqb
  set sa := Real.sqrt (a ^ 2 + a + 1)
  set sb := Real.sqrt (b ^ 2 + b + 1)
  have hsa : a + 1 / 2 ≤ sa := by nlinarith
  have hsb : b + 1 / 2 ≤ sb := by nlinarith
  have hpos : 0 < sa + sb := by linarith
  have hprod : 0 ≤ (b - a) * (2 * sa + 2 * sb - a - b - 1) := by
    apply mul_nonneg <;> linarith
  have key : sb - sa ≤ 2 * (b - a) := by
    by_contra hc
    push_neg at hc
    have := mul_lt_mul_of_pos_right hc hpos
    nlinarith
  apply div_le_div_of_nonneg_right _ (by norm_num)
  linarith

end Aux_UT_lemma1

open UtilityTokens.ICOChoice in
theorem solution :
    thetaInterior thetaTilde = 1 ∧
    (1 < thetaTilde ∧ thetaTilde < 3) ∧
    (∀ Θ : ℝ, 1 < Θ → Θ ≤ thetaTilde → thetaStar Θ = 1) ∧
    (∀ Θ : ℝ, thetaTilde < Θ → 1 < thetaStar Θ) ∧
    MonotoneOn thetaStar (Set.Ioi 1) := by
  have hr2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hr0 := Real.sqrt_nonneg 5
  have hr : 2 < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hr3 : Real.sqrt 5 < 3 := by nlinarith
  have hT : thetaTilde = (Real.sqrt 5 + 3) / 2 := rfl
  have hT1 : 1 < thetaTilde := by rw [hT]; linarith
  have hT3 : thetaTilde < 3 := by rw [hT]; linarith
  refine ⟨?_, ⟨hT1, hT3⟩, ?_, ?_, ?_⟩
  · unfold thetaInterior
    have : thetaTilde ^ 2 + thetaTilde + 1 = (2 * thetaTilde - 2) ^ 2 := by
      rw [hT]; nlinarith
    rw [this, Real.sqrt_sq (by linarith)]
    ring
  · intro Θ h1 h2
    unfold thetaStar
    apply max_eq_left
    unfold thetaInterior
    have : 2 * Θ - 2 ≤ Real.sqrt (Θ ^ 2 + Θ + 1) := by
      rw [Real.le_sqrt' (by linarith)]
      have hA : 0 ≤ thetaTilde - Θ := by linarith
      have hB : 0 ≤ Θ - (3 - Real.sqrt 5) / 2 := by linarith
      have := mul_nonneg hA hB
      rw [hT] at this
      nlinarith
    linarith
  · intro Θ h
    unfold thetaStar
    apply lt_max_of_lt_right
    unfold thetaInterior
    have : Real.sqrt (Θ ^ 2 + Θ + 1) < 2 * Θ - 2 := by
      rw [Real.sqrt_lt' (by linarith)]
      have hA : 0 < Θ - thetaTilde := by linarith
      have hB : 0 < Θ - (3 - Real.sqrt 5) / 2 := by rw [hT] at h; linarith
      have := mul_pos hA hB
      rw [hT] at this
      nlinarith
    linarith
  · intro a ha b hb hab
    unfold thetaStar
    exact max_le_max (le_refl 1) (Aux_UT_lemma1.interior_mono (by simp at ha; linarith) hab)
