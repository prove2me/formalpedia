-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D27_q4_cases_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T14:20:58.728006+00:00
-- url     : https://prove2.me/submissions/fa461496-707f-4770-af9e-dc671316b5ba

import Mathlib

theorem solution (q4 : Nat) (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (hq4le : q4 ≤ 89) :
    q4 = 31 ∨ q4 = 37 ∨ q4 = 41 ∨ q4 = 43 ∨ q4 = 47 ∨ q4 = 53 ∨
      q4 = 59 ∨ q4 = 61 ∨ q4 = 67 ∨ q4 = 71 ∨ q4 = 73 ∨
      q4 = 79 ∨ q4 = 83 ∨ q4 = 89 := by
  have hge : 30 ≤ q4 := by omega
  by_cases h1 : q4 ≤ 45
  · interval_cases q4 <;> norm_num at hq4prime <;> norm_num
  · have h46 : 46 ≤ q4 := by omega
    by_cases h2 : q4 ≤ 60
    · interval_cases q4 <;> norm_num at hq4prime <;> norm_num
    · have h61 : 61 ≤ q4 := by omega
      by_cases h3 : q4 ≤ 75
      · interval_cases q4 <;> norm_num at hq4prime <;> norm_num
      · have h76 : 76 ≤ q4 := by omega
        interval_cases q4 <;> norm_num at hq4prime <;> norm_num
