-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D45_q4_31_canonical_floors_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:18:14.071984+00:00
-- url     : https://prove2.me/submissions/e5586082-95d2-42d9-ae48-cc513193b336

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D45_q4_31_canonical_floors_absurd_v2

open OddPerfectNumber

theorem solution (m a b c e D p q4 sigma : Nat)
  (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
  (hsigma : sigma =
   (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
   (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
   (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
   (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
  (hrel : D * sigma = p * m ^ 2)
  (hD : D = 45) (hp_eq : p = 2 * D - 1) (hq4 : q4 = 31)
  (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    False :=
  OddPerfectNumber.k_one_q2_five_q3_twentynine_D45_q4_31_canonical_floors_absurd_v2 m a b c e D p q4 sigma hfac hsigma hrel hD hp_eq hq4 ha hb hc he
