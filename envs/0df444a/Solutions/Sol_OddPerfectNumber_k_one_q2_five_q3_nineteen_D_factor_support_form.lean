-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_D_factor_support_form
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:32:27.052179+00:00
-- url     : https://prove2.me/submissions/885a3307-9928-4019-a06a-bc6a3bf37616

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D_factor_support_form_v4

open OddPerfectNumber

theorem solution (m a b c e D q4 : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hDdvd : D ∣ m ^ 2) (hDpos : 0 < D) (hq4prime : q4.Prime) (hq4gt : 19 < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) :
    ∃ i j k l, D = 3^i * 5^j * 19^k * q4^l ∧ i ≤ 2*a ∧ j ≤ 2*b ∧ k ≤ 2*c ∧ l ≤ 2*e :=
  OddPerfectNumber.k_one_q2_five_q3_nineteen_D_factor_support_form_v4 m a b c e D q4 hfac hDdvd hDpos hq4prime hq4gt hDsupport
