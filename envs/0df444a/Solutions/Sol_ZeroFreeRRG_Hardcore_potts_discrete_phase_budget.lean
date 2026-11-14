-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_discrete_phase_budget
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:28:58.659796+00:00
-- url     : https://prove2.me/submissions/ae04fab1-ec69-434e-80d6-c143ea0ba708

import Mathlib
set_option autoImplicit false

theorem solution (d : ℕ) (hd : 3 ≤ d) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsmall : δ < (0.35:ℝ)/(d:ℝ)) :
    let r := δ / (((7:ℝ)/8)*(1-δ))
    0 ≤ r ∧ r ≤ 96/625 ∧ (d:ℝ)*(25/23)*r < 1/2 := by
  dsimp only
  have hd' : (3:ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0:ℝ) < d := by linarith
  have hprod : δ*(d:ℝ) < 0.35 := (lt_div_iff₀ hdp).1 hsmall
  have hδbound : δ < 7/60 := by nlinarith [mul_nonneg hδ (show (d:ℝ)-3 ≥ 0 by linarith)]
  have hδone : 0 < 1-δ := by linarith
  have hden : 0 < ((7:ℝ)/8)*(1-δ) := by positivity
  constructor
  · exact div_nonneg hδ hden.le
  constructor
  · apply (div_le_iff₀ hden).2
    linarith
  · rw [← mul_div_assoc]
    apply (div_lt_iff₀ hden).2
    nlinarith
