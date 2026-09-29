-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D87_q4_29_abundance_absurd_v3
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:32:21.04089+00:00
-- url     : https://prove2.me/submissions/8149937a-f99d-4d1d-89ff-50e2a8c29399

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D87_q4_29_abundance_absurd_v5

open OddPerfectNumber

theorem solution (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hD : D = 87) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4eq : q4 = 29) (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) :
    False :=
  OddPerfectNumber.k_one_q2_five_q3_twentynine_D87_q4_29_abundance_absurd_v5 m a b c e D p q4 sigma hfac hsigma hrel hD hp_eq hq4prime hq4eq ha hb hc he
