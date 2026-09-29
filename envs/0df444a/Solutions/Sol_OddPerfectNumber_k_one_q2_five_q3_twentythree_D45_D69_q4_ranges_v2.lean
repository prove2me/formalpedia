-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D45_D69_q4_ranges_v2
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:32:25.938308+00:00
-- url     : https://prove2.me/submissions/874b4edf-37be-4d02-ba89-e8d1d1bf91a5

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D45_D69_q4_ranges_v4

open OddPerfectNumber

theorem solution (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDcases : D = 45 ∨ D = 69) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hDq : D < q4) (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e) :
    ((D = 45 ∧ 46 ≤ q4 ∧ q4 ≤ 112) ∨ (D = 69 ∧ 70 ≤ q4 ∧ q4 ≤ 78)) :=
  OddPerfectNumber.k_one_q2_five_q3_twentythree_D45_D69_q4_ranges_v4 m a b c e D p q4 sigma hfac hsigma hrel hDcases hp_eq hq4prime hDq ha hb hc he
