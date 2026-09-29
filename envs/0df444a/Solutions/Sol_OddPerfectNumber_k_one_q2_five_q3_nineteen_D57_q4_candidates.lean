-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_D57_q4_candidates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T15:54:33.850918+00:00
-- url     : https://prove2.me/submissions/2627b39c-aeb5-4114-95c9-69dad48ae150

import Mathlib

theorem solution (q4 : Nat)
    (hq4prime : q4.Prime) (hlow : 580 ≤ q4) (hhigh : q4 ≤ 602) :
    q4 = 587 ∨ q4 = 593 ∨ q4 = 599 ∨ q4 = 601 := by
  interval_cases q4 <;>
    norm_num at hq4prime <;>
    norm_num
