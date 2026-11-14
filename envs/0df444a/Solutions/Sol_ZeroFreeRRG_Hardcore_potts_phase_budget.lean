-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_phase_budget
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:05:26.997665+00:00
-- url     : https://prove2.me/submissions/c071a99a-4d51-4196-bcff-38eeaec5941a

import Mathlib
set_option autoImplicit false

theorem solution (d : ℕ) (hd : 3 ≤ d) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsmall : δ < (0.35:ℝ)/(d:ℝ)) :
    δ*(d:ℝ) / (((7:ℝ)/8)*(1-δ)) < 1/2 := by
  have hd' : (3:ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0:ℝ) < d := by linarith
  have hprod : δ*(d:ℝ) < 0.35 := (lt_div_iff₀ hdp).1 hsmall
  have hδbound : δ < 7/60 := by nlinarith [mul_nonneg hδ (show (d:ℝ)-3 ≥ 0 by linarith)]
  have hδone : 0 < 1-δ := by linarith
  have hden : 0 < ((7:ℝ)/8)*(1-δ) := by positivity
  apply (div_lt_iff₀ hden).2
  linarith
