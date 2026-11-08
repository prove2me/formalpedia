-- Prove2me | solution 1 for ProcessingNetworks.EntropyIneq.lemma_B_16
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:14:02.488268+00:00
-- url     : https://prove2.me/submissions/e17a3847-d5bd-4a33-b0d7-82db466252b6

import Mathlib

theorem solution (a ahat d dhat : ℝ) (ha : 0 ≤ a) (hahat : a ≤ ahat) (hd : 0 < d)
    (hdhat : d ≤ dhat) :
    (a - d) * Real.log d ≤ ahat * Real.log (max 1 dhat) + 1 / Real.exp 1 := by
  have hepos : 0 < 1 / Real.exp 1 := by positivity
  have hlm : 0 ≤ Real.log (max 1 dhat) := Real.log_nonneg (le_max_left _ _)
  have key : -(d * Real.log d) ≤ 1 / Real.exp 1 := by
    have h := Real.log_le_sub_one_of_pos
      (show 0 < 1 / (Real.exp 1 * d) from div_pos one_pos (mul_pos (Real.exp_pos 1) hd))
    rw [one_div, Real.log_inv, Real.log_mul (Real.exp_pos 1).ne' hd.ne', Real.log_exp] at h
    have h2 : -Real.log d ≤ (Real.exp 1 * d)⁻¹ := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hd.le
    have e : d * (Real.exp 1 * d)⁻¹ = 1 / Real.exp 1 := by
      field_simp
    linarith
  rcases le_or_gt 1 d with h1 | h1
  · have hlog : 0 ≤ Real.log d := Real.log_nonneg h1
    have hmono : Real.log d ≤ Real.log (max 1 dhat) :=
      Real.log_le_log hd (le_trans hdhat (le_max_right _ _))
    have hp1 := mul_le_mul hahat hmono hlog (by linarith : 0 ≤ ahat)
    have hp2 := mul_nonneg hd.le hlog
    nlinarith
  · have hlog : Real.log d < 0 := Real.log_neg hd h1
    have hp1 : a * Real.log d ≤ 0 := by nlinarith
    have hp2 : 0 ≤ ahat * Real.log (max 1 dhat) := mul_nonneg (le_trans ha hahat) hlm
    nlinarith
