-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_lo_v1
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-22T05:47:59.945271+00:00
-- url     : https://prove2.me/submissions/5282708b-6253-4867-8bd2-9b3c0e918ace

import Mathlib

/-- The statement is false: `D = 12` satisfies every hypothesis
(`12 ≤ 12 ≤ 43`, `12 % 3 = 0`, and `2*12 - 1 = 23` is prime) yet is not in the
listed set of values. -/
theorem solution : ¬ ∀ (D : Nat), 12 ≤ D → D ≤ 43 →
    (D % 3 = 0 ∨ D % 5 = 0 ∨ D % 29 = 0 ∨ D % 31 = 0) → Nat.Prime (2 * D - 1) →
    (D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87) := by
  intro h
  have hc := h 12 (by norm_num) (by norm_num) (Or.inl (by norm_num)) (by norm_num)
  omega
