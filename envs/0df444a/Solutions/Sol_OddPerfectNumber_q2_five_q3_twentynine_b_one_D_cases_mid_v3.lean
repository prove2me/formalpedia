-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_mid_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T05:04:25.138973+00:00
-- url     : https://prove2.me/submissions/a01bd54e-a586-4145-8cb5-4eee3bd4bf3b

import Mathlib

theorem solution (D : Nat)
    (hlo : 44 ≤ D) (hhi : D ≤ 74)
    (hD : D ∣ 1820475)
    (hp : Nat.Prime (2 * D - 1)) :
    D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87 := by
  interval_cases D <;> try norm_num at hD <;> try norm_num at hp <;> try norm_num <;> omega
