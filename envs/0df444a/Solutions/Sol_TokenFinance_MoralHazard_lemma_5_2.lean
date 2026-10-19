-- Prove2me | solution 2 for TokenFinance.MoralHazard.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T12:13:40.323744+00:00
-- url     : https://prove2.me/submissions/ee066521-786f-45c6-9e3e-75d560179669

import Mathlib
set_option autoImplicit false

theorem solution (τ lam : ℝ) (hτ : 0 < τ) (hτl : τ < lam) (hl1 : lam < 1) :
    lam ^ 3 > (lam - τ) ^ 3 / (1 - τ) ^ 3 := by
  have h1 : 0 < 1 - τ := by linarith
  have h0 : 0 ≤ lam - τ := by linarith
  have hlt : lam - τ < lam * (1 - τ) := by nlinarith
  have : (lam - τ) ^ 3 < (lam * (1 - τ)) ^ 3 := by
    exact pow_lt_pow_left₀ hlt h0 (by norm_num)
  rw [gt_iff_lt, div_lt_iff₀ (by positivity)]
  calc (lam - τ) ^ 3 < (lam * (1 - τ)) ^ 3 := this
    _ = lam ^ 3 * (1 - τ) ^ 3 := by ring
