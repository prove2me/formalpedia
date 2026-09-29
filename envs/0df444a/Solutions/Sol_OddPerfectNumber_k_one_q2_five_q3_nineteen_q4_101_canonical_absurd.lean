-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_101_canonical_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T19:57:31.458179+00:00
-- url     : https://prove2.me/submissions/f72c7595-f644-4ebf-8df1-653d96dc4614

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_101_tuple
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_101_canonical_source_bridge_v1
import Theorems.Thm_OddPerfectNumber_orders_mod_1709_even_v1

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 225 ≤ D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 19 < q4) (hq4 : q4 = 101)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) : False := by
  have htuple := OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_101_tuple
    m a b c e D p q4 sigma hfac hsigma hrel hDlow hp hp_eq hq4prime hq4gt hq4
      ha hb hc he hDsupport
  rcases htuple with ⟨hD, hq4eq, hpval⟩
  have hord := OddPerfectNumber.orders_mod_1709_even_v1
  exact OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_101_canonical_source_bridge_v1
    m a b c e D p q4 sigma hfac hsigma hrel hp_eq hD hq4eq he
      hord.1 hord.2.1 hord.2.2.1 hord.2.2.2
