-- Prove2me | solution 1 for OddPerfectNumber.k_one_deficiency_dvd_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T22:35:48.614973+00:00
-- url     : https://prove2.me/submissions/e3e42836-48fc-4f85-820a-0c2dea637c74

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_D_dvd_m2

theorem solution (m D p sigma : Nat)
    (hrel : D * sigma = p * m ^ 2)
    (hp : p.Prime)
    (hp_eq : p = 2 * D - 1) :
    D ∣ m ^ 2 := by
  exact OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_D_dvd_m2
    m D p sigma hrel hp hp_eq
