-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D225_q4_37_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:32:17.28118+00:00
-- url     : https://prove2.me/submissions/7705ccc5-172a-4fc7-943a-d216a64cf9e0

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D225_q4_37_absurd_v4

open OddPerfectNumber

theorem solution (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hD : D = 225) (hp_eq : p = 2 * D - 1) (hp : p.Prime) (hq4eq : q4 = 37) :
    False :=
  OddPerfectNumber.k_one_q2_five_q3_twentynine_D225_q4_37_absurd_v4 m a b c e D p q4 sigma hfac hsigma hrel hD hp_eq hp hq4eq
