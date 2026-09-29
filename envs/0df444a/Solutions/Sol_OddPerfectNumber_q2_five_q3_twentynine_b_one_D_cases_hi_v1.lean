-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_hi_v1
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-22T05:47:59.897426+00:00
-- url     : https://prove2.me/submissions/2ddfae6a-8f27-4b22-9354-1d4bce230bb4

import Mathlib

/-- The statement is false: `D = 84` satisfies every hypothesis
(`75 ≤ 84 ≤ 105`, `84 % 3 = 0`, and `2*84 - 1 = 167` is prime) yet is not in the
listed set of values. -/
theorem solution : ¬ ∀ (D : Nat), 75 ≤ D → D ≤ 105 →
    (D % 3 = 0 ∨ D % 5 = 0 ∨ D % 29 = 0 ∨ D % 31 = 0) → Nat.Prime (2 * D - 1) →
    (D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87) := by
  intro h
  have hc := h 84 (by norm_num) (by norm_num) (Or.inl (by norm_num)) (by norm_num)
  omega
