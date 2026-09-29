-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_canonical_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T21:04:42.590346+00:00
-- url     : https://prove2.me/submissions/38297103-a251-4d0d-9422-89c1d1c0ba23

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_case_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_101_canonical_absurd

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 225 ≤ D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 19 < q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c)
    (he : 1 ≤ e)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) : False := by
  have ht := OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_case_v2
    m a b c e D p q4 sigma hfac hsigma hrel hDlow hp hp_eq hq4prime hq4gt
      ha hb hc he hDsupport
  rcases ht with ⟨hD, hq4, hpval⟩
  exact OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_101_canonical_absurd
    m a b c e D p q4 sigma hfac hsigma hrel hDlow hp hp_eq hq4prime hq4gt
      hq4 ha hb hc he hDsupport
