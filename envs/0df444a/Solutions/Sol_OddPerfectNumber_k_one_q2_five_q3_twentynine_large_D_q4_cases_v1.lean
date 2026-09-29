-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_cases_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T10:31:22.057486+00:00
-- url     : https://prove2.me/submissions/2d4d309c-21d0-42df-ae6b-9970fd5947c4

import Mathlib

theorem solution (q4 : Nat) (hq4prime : q4.Prime)
    (hq4gt : 29 < q4) (hq4le : q4 ≤ 43) :
    q4 = 31 ∨ q4 = 37 ∨ q4 = 41 ∨ q4 = 43 := by
  have hq4ge : 30 ≤ q4 := by omega
  interval_cases q4 <;> norm_num at hq4prime <;> norm_num
