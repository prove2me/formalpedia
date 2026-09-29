-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_smooth_D_v1
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-22T05:50:29.025813+00:00
-- url     : https://prove2.me/submissions/7592acc0-90c6-45dd-82b0-522ffba8d3a9

import Mathlib

/-- False as stated: the hypotheses are degenerate when `m = 0`. Then `m ^ 2 = 0`,
every `D` divides `0`, and `Nat.primeFactors 0 = ∅` makes the support condition
vacuous, so `D = 7` satisfies everything while `7 ∤ 1820475 = 3^4 * 5^2 * 29 * 31`. -/
theorem solution : ¬ ∀ (D m q4 : Nat), D < 107 → 0 < D → D ∣ m ^ 2 →
    (∀ x ∈ (m ^ 2).primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4) → q4 = 31 →
    D ∣ 1820475 := by
  intro h
  have hc := h 7 0 31 (by norm_num) (by norm_num) (by simp) (by simp) rfl
  norm_num at hc
