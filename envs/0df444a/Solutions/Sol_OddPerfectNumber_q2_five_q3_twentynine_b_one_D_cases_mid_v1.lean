-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_mid_v1
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-22T05:47:59.933816+00:00
-- url     : https://prove2.me/submissions/440033fd-7c3e-44c4-8674-a7de71f2db52

import Mathlib

/-- The statement is false: `D = 51` satisfies every hypothesis
(`44 ≤ 51 ≤ 74`, `51 % 3 = 0`, and `2*51 - 1 = 101` is prime) yet is not in the
listed set of values. -/
theorem solution : ¬ ∀ (D : Nat), 44 ≤ D → D ≤ 74 →
    (D % 3 = 0 ∨ D % 5 = 0 ∨ D % 29 = 0 ∨ D % 31 = 0) → Nat.Prime (2 * D - 1) →
    (D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87) := by
  intro h
  have hc := h 51 (by norm_num) (by norm_num) (Or.inl (by norm_num)) (by norm_num)
  omega
