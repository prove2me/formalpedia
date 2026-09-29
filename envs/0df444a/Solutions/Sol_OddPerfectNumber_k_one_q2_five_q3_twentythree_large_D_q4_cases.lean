-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_q4_cases
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T18:59:31.394156+00:00
-- url     : https://prove2.me/submissions/6d1974d8-86f6-4ca3-839c-7a7dc760757d

import Mathlib

theorem solution (q4 : Nat)
    (hq4prime : q4.Prime) (hq4gt : 47 < q4) (hq4le : q4 ≤ 61) :
    q4 = 53 ∨ q4 = 59 ∨ q4 = 61 := by
  interval_cases q4 <;> norm_num at hq4prime <;> norm_num
