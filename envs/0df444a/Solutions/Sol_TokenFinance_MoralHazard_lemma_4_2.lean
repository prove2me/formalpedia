-- Prove2me | solution 2 for TokenFinance.MoralHazard.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T12:14:00.230287+00:00
-- url     : https://prove2.me/submissions/98d562b1-be17-40ee-931b-09c716498c17

import Mathlib
set_option autoImplicit false

theorem solution (δ lam : ℝ) (hδ : 0 < δ) (hδl : δ < lam) (hl1 : lam < 1) :
    lam ^ 3 > (lam - δ) ^ 2 / (1 - δ) ^ 2 * ((lam + 2 * δ) / (1 + 2 * δ)) := by
  have hl0 : 0 < lam := by linarith
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < 1 + 2 * δ := by linarith
  have h3 : 0 < (1 - δ) ^ 2 := by positivity
  have hpos : 0 < 3 * lam ^ 2 + 3 * lam - 2 * δ * (lam ^ 2 + lam + 1) := by
    have : 0 < lam * (1 - lam) * (1 + 2 * lam) := by
      have : 0 < lam := by linarith
      have : 0 < 1 - lam := by linarith
      positivity
    nlinarith [mul_pos (sub_pos.2 hδl) (by positivity : (0:ℝ) < lam ^ 2 + lam + 1)]
  have key : 0 < δ ^ 2 * (1 - lam) * (3 * lam ^ 2 + 3 * lam - 2 * δ * (lam ^ 2 + lam + 1)) := by
    have : 0 < 1 - lam := by linarith
    positivity
  rw [gt_iff_lt, div_mul_div_comm, div_lt_iff₀ (by positivity)]
  nlinarith [key]
