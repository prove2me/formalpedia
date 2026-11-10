-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P47.nonuniform_input_entropy
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T02:05:28.768473+00:00
-- url     : https://prove2.me/submissions/16c72d31-471d-46d3-99cc-d865c0fe546f

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

open scoped ComplexConjugate

open scoped BigOperators

namespace Aux_P47_nie

theorem hl (a b : ℝ) : a * b * Real.log (a * b) = a * b * Real.log a + a * b * Real.log b := by
  rcases eq_or_ne a 0 with ha | ha
  · simp [ha]
  rcases eq_or_ne b 0 with hb | hb
  · simp [hb]
  rw [Real.log_mul ha hb]; ring

end Aux_P47_nie

open QAlgorithms QAlgorithms.Papers.Independent.Intakethird100.P47 in
theorem solution :
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      pairEntropy (binarySettingLaw r r) = 2 * binEntropy2 r ∧
      (r ≠ 1 / 2 → pairEntropy (binarySettingLaw r r) < 2)) ∧
    (0 < (Real.sqrt 5 - 1) / 2 ∧ (Real.sqrt 5 - 1) / 2 < 1) ∧
    pairEntropy (binarySettingLaw ((Real.sqrt 5 - 1) / 2) ((Real.sqrt 5 - 1) / 2)) < 2 := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have heq : ∀ r : ℝ, pairEntropy (binarySettingLaw r r) = 2 * binEntropy2 r := by
    intro r
    unfold pairEntropy QAlgorithms.binEntropy2 binarySettingLaw
    simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
    simp only [← mul_div_assoc, Aux_P47_nie.hl]
    rw [Real.binEntropy, Real.log_inv, Real.log_inv]
    ring
  have hlt : ∀ r : ℝ, r ≠ 1 / 2 → pairEntropy (binarySettingLaw r r) < 2 := by
    intro r hr
    rw [heq]
    unfold QAlgorithms.binEntropy2
    have h1 : Real.binEntropy r < Real.log 2 :=
      Real.binEntropy_lt_log_two.mpr (by rw [← one_div]; exact hr)
    have h2 : Real.binEntropy r / Real.log 2 < 1 := (div_lt_one hL).mpr h1
    linarith
  have h5 : (1 : ℝ) < Real.sqrt 5 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h53 : Real.sqrt 5 < 3 := by
    rw [show (3 : ℝ) = Real.sqrt 9 by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h52 : Real.sqrt 5 ≠ 2 := by
    intro h
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    rw [h] at this; norm_num at this
  refine ⟨fun r _ _ => ⟨heq r, hlt r⟩, ⟨by linarith, by linarith⟩, hlt _ ?_⟩
  intro h
  apply h52
  linarith
