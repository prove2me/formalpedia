-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_small_D_cases_canonical_v2
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:32:19.529389+00:00
-- url     : https://prove2.me/submissions/803efeb3-32db-4c29-ba4b-b2ec5e416050

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_small_D_cases_canonical_v7

open OddPerfectNumber

theorem solution (D p q4 : Nat) (hDgt : 15 < D) (hDlt : D < 75) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4gt : 29 < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4) :
    D = 27 ∨ D = 31 ∨ D = 37 ∨ D = 45 :=
  OddPerfectNumber.k_one_q2_five_q3_twentynine_small_D_cases_canonical_v7 D p q4 hDgt hDlt hDodd hp hp_eq hq4gt hDsupport
