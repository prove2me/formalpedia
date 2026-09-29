-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D_dvd_square_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T11:23:24.964327+00:00
-- url     : https://prove2.me/submissions/0150c1b6-364c-4493-82f9-a3509239afb7

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_deficiency_dvd_square

theorem solution (m D p sigma : Nat)
    (hrel : D * sigma = p * m ^ 2)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) :
    D ∣ m ^ 2 := by
  exact OddPerfectNumber.k_one_deficiency_dvd_square m D p sigma hrel hp hp_eq
