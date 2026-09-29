-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_hi_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T05:04:29.179236+00:00
-- url     : https://prove2.me/submissions/df0ba917-620f-4f2f-9380-26242ea39af3

import Mathlib

theorem solution (D : Nat)
    (hlo : 75 ≤ D) (hhi : D ≤ 105)
    (hD : D ∣ 1820475)
    (hp : Nat.Prime (2 * D - 1)) :
    D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87 := by
  interval_cases D <;> try norm_num at hD <;> try norm_num at hp <;> try norm_num <;> omega
