-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_D75_q4_candidate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T16:04:13.144234+00:00
-- url     : https://prove2.me/submissions/b68e21b1-e35e-4d79-8cdf-70deb75916fb

import Mathlib

theorem solution (q4 : Nat)
    (hq4prime : q4.Prime) (hlow : 261 ≤ q4) (hhigh : q4 ≤ 264) :
    q4 = 263 := by
  interval_cases q4 <;>
    norm_num at hq4prime <;>
    norm_num
