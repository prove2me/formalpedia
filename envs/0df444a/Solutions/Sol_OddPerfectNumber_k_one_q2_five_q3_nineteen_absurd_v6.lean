-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_absurd_v6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T08:23:13.580225+00:00
-- url     : https://prove2.me/submissions/146d0943-57b2-4e2b-aaca-b6622e259f96

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D_lt_147_absurd_canonical_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_middle_D_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_canonical_absurd_v2

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDodd : Odd D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 19 < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  by_cases hDlt147 : D < 147
  · exact OddPerfectNumber.k_one_q2_five_q3_nineteen_D_lt_147_absurd_canonical_v1
      m a b c e D p q4 sigma hfac hsigma hrel hDlt147 hDodd hp hp_eq
      hq4prime hq4gt hDsupport ha hb hc he
  by_cases hDlt225 : D < 225
  · exact OddPerfectNumber.k_one_q2_five_q3_nineteen_middle_D_absurd_v1
      m a b c e D p q4 sigma hfac hsigma hrel hDlt225 hDodd hp hp_eq
      hq4prime hq4gt hDsupport ha hb hc he
  have hDlow225 : 225 ≤ D := by omega
  have hlarge := OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_canonical_absurd_v2
      m a b c e D p q4 sigma hfac hsigma hrel hDlow225 hp hp_eq hq4prime
      hq4gt ha hb hc he hDsupport
  exact hlarge
