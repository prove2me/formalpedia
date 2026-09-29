-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_D135_no_q4_candidate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T16:04:45.831719+00:00
-- url     : https://prove2.me/submissions/727c2785-c533-4f15-9414-1f7b6be3a002

import Mathlib

theorem solution (q4 : Nat)
    (hq4prime : q4.Prime) (hlow : 146 ≤ q4) (hhigh : q4 ≤ 148) :
    False := by
  interval_cases q4 <;>
    norm_num at hq4prime <;>
    norm_num
