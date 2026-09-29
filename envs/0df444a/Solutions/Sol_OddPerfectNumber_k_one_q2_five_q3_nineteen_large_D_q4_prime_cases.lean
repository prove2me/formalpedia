-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_q4_prime_cases
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T08:10:49.876835+00:00
-- url     : https://prove2.me/submissions/8d628439-495b-46cd-9aa7-812cd876cb42

import Mathlib

theorem solution (q4 : Nat)
    (hq4prime : q4.Prime)
    (hq4gt : 19 < q4)
    (hq4le : q4 ≤ 113) :
    q4 = 23 ∨ q4 = 29 ∨ q4 = 31 ∨ q4 = 37 ∨ q4 = 41 ∨ q4 = 43 ∨
      q4 = 47 ∨ q4 = 53 ∨ q4 = 59 ∨ q4 = 61 ∨ q4 = 67 ∨ q4 = 71 ∨
      q4 = 73 ∨ q4 = 79 ∨ q4 = 83 ∨ q4 = 89 ∨ q4 = 97 ∨ q4 = 101 ∨
      q4 = 103 ∨ q4 = 107 ∨ q4 = 109 ∨ q4 = 113 := by
  have hlow : 20 ≤ q4 := by omega
  interval_cases q4
  all_goals (norm_num at hq4prime <;> norm_num)
