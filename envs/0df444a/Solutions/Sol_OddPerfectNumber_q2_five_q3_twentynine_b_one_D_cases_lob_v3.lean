-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_lob_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T05:04:20.755762+00:00
-- url     : https://prove2.me/submissions/d1bab954-bd86-4712-b890-be08505f390b

import Mathlib

theorem solution (D : Nat)
    (hlo : 28 ≤ D) (hhi : D ≤ 43)
    (hD : D ∣ 1820475)
    (hp : Nat.Prime (2 * D - 1)) :
    D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87 := by
  interval_cases D <;> try norm_num at hD <;> try norm_num at hp <;> try norm_num <;> omega
