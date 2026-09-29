-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_absurd_v5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T01:04:24.679788+00:00
-- url     : https://prove2.me/submissions/5fcdee12-6c2f-499d-9920-f6779eab85e1

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_canonical_absurd_v4
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_canonical_absurd_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_survivors
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_q4_ranges_v6

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDodd : Odd D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 19 < q4) (hDq : D < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  by_cases hDlt : D < 225
  · have hcases :=
      OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_survivors
        m (2*a) (2*b) (2*c) (2*e) D p q4 sigma hfac hsigma hrel hDlt hDodd
        hp hp_eq hq4prime hq4gt hDq hDsupport (by omega) (by omega) (by omega)
        (by omega)
    have hrange :=
      OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_q4_ranges_v6
        m a b c e D p q4 sigma hfac hsigma hrel hcases hp_eq hq4prime hDq
        ha hb hc he
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_canonical_absurd_v4
      m a b c e D p q4 sigma hfac hsigma hrel hDlt hDodd hp hp_eq
      hq4prime hq4gt hDq hDsupport ha hb hc he hrange
  · have hDlow : 225 ≤ D := by omega
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_canonical_absurd_v2
      m a b c e D p q4 sigma hfac hsigma hrel hDlow hp hp_eq hq4prime hq4gt
      ha hb hc he hDsupport
