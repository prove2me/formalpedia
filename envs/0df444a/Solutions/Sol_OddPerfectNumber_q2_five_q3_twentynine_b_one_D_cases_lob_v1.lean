-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_lob_v1
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-22T05:47:59.940577+00:00
-- url     : https://prove2.me/submissions/aea1e494-6fa7-4677-9021-f12b9aab735f

import Mathlib

/-- The statement is false: `D = 30` satisfies every hypothesis
(`28 ≤ 30 ≤ 43`, `30 % 3 = 0`, and `2*30 - 1 = 59` is prime) yet is not in the
listed set of values. -/
theorem solution : ¬ ∀ (D : Nat), 28 ≤ D → D ≤ 43 →
    (D % 3 = 0 ∨ D % 5 = 0 ∨ D % 29 = 0 ∨ D % 31 = 0) → Nat.Prime (2 * D - 1) →
    (D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87) := by
  intro h
  have hc := h 30 (by norm_num) (by norm_num) (Or.inl (by norm_num)) (by norm_num)
  omega
