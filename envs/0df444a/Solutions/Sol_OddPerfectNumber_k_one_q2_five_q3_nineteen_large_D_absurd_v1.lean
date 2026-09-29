-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T03:52:41.888085+00:00
-- url     : https://prove2.me/submissions/48dc250e-bcf3-41c6-a8f8-779cb4438ebc

import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_101_canonical_source_bridge_v1
import Theorems.Thm_OddPerfectNumber_orders_mod_1709_even_v1

theorem solution
    (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1)
    (hD : D = 855) (hq4 : q4 = 101) (he : 1 ≤ e) :
    False := by
  have hord := OddPerfectNumber.orders_mod_1709_even_v1
  exact OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_101_canonical_source_bridge_v1
    m a b c e D p q4 sigma hfac hsigma hrel hp_eq hD hq4 he
    hord.1 hord.2.1 hord.2.2.1 hord.2.2.2
