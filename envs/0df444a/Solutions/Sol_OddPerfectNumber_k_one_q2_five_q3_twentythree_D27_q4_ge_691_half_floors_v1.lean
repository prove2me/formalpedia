-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_q4_ge_691_half_floors_v1
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:00:33.265129+00:00
-- url     : https://prove2.me/submissions/07c759fe-c828-40d3-87ca-e5754c42b9a8

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_ge_691_half_floors_v2

open OddPerfectNumber

theorem solution (m a b c e D p q4 sigma : Nat)
  (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
  (hsigma : sigma =
   (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
   (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
   (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
   (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
  (hrel : D * sigma = p * m ^ 2)
  (hD : D = 27) (hp_eq : p = 2 * D - 1)
  (hq4prime : q4.Prime) (hq4gt : 23 < q4)
  (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    691 ≤ q4 :=
  OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_q4_ge_691_half_floors_v2 m a b c e D p q4 sigma hfac hsigma hrel hD hp_eq hq4prime hq4gt ha hb hc he
