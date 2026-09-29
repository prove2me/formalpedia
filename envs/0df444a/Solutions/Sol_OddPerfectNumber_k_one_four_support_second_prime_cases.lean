-- Prove2me | solution 1 for OddPerfectNumber.k_one_four_support_second_prime_cases
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T19:03:44.445157+00:00
-- url     : https://prove2.me/submissions/2595326d-1ec5-4477-b42d-096ba34319f8

import Mathlib

theorem solution (q1 q2 : Nat)
    (hq1 : q1.Prime) (hq2 : q2.Prime)
    (horder : q1 < q2) (hq1eq : q1 = 3) (hq2le : q2 ≤ 23) :
    q2 = 5 ∨ q2 = 7 ∨ q2 = 11 ∨ q2 = 13 ∨
      q2 = 17 ∨ q2 = 19 ∨ q2 = 23 := by
  subst q1
  have hq2lo : 4 ≤ q2 := by omega
  interval_cases q2 <;> norm_num at hq2 <;> norm_num
