-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_q4_ranges_v3
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:32:24.542816+00:00
-- url     : https://prove2.me/submissions/bf5b93ee-9f0b-47c6-997b-ac759faa456d

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_q4_ranges_v6

open OddPerfectNumber

theorem solution (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDcases : D = 57 ∨ D = 75 ∨ D = 135) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hDq : D < q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    ((D = 57 ∧ 580 ≤ q4 ∧ q4 ≤ 602) ∨ (D = 75 ∧ 261 ≤ q4 ∧ q4 ≤ 264) ∨ (D = 135 ∧ 146 ≤ q4 ∧ q4 ≤ 148)) :=
  OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_q4_ranges_v6 m a b c e D p q4 sigma hfac hsigma hrel hDcases hp_eq hq4prime hDq ha hb hc he
