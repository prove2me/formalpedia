-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_le_D_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T07:52:18.32971+00:00
-- url     : https://prove2.me/submissions/a16f2d5a-63cf-4b0d-b569-57ca4d4a6db4

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_divides_D_cases_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_divisor_small_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_not_divides_D_absurd_v1

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlt : D < 111) (hDodd : Odd D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 23 < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (hq4le : q4 ≤ D) (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c)
    (he : 1 ≤ e) : False := by
  by_cases hq4div : q4 ∣ D
  · have hcases := OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_divides_D_cases_v1
      D p q4 hDlt hDodd hp hp_eq hq4prime hq4gt hq4div
    exact OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_divisor_small_absurd_v1
      m a b c e D p q4 sigma hfac hsigma hrel hcases hp_eq ha hb hc he
  · exact OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_not_divides_D_absurd_v1
      m a b c e D p q4 sigma hfac hsigma hrel hDlt hDodd hp hp_eq hq4prime hq4gt
      hq4div hDsupport hq4le ha hb hc he
