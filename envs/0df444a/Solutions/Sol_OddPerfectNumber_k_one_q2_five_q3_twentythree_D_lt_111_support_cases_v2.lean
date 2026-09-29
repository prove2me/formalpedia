-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v2
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:32:28.247893+00:00
-- url     : https://prove2.me/submissions/9d1aa31c-6a9b-46ce-aee9-dccc24350ee8

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v5

open OddPerfectNumber

theorem solution (D p q4 : Nat)
  (hDlt : D < 111)
  (hDodd : Odd D)
  (hp : p.Prime)
  (hp_eq : p = 2 * D - 1)
  (hq4gt : 23 < q4)
  (hDq : D < q4)
  (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) :
    D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 27 ∨ D = 45 ∨ D = 69 ∨ D = 75 :=
  OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v5 D p q4 hDlt hDodd hp hp_eq hq4gt hDq hDsupport
