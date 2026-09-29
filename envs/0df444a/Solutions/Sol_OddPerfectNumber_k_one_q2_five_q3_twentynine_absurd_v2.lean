-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T16:17:19.113379+00:00
-- url     : https://prove2.me/submissions/3c8b1834-3fca-4f05-91d3-33de72f58c36

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D_gt_15_v6
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_small_D_cases_canonical_v7
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D27_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D31_absurd_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D37_absurd_v3
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D45_absurd_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D45_canonical_absurd_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_absurd_v2

theorem solution (m d sigma D p q4 a b c e : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDodd : Odd D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4)
    (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2) (hm0 : m ≠ 0)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4) : False := by
  by_cases hDlarge : 75 ≤ D
  · exact OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_absurd_v2
      m a b c e D p q4 sigma hfac hsigma hrel hDlarge hDodd hp hp_eq
      hq4prime hq4gt hDsupport ha hb hc he
  · have hDlt : D < 75 := by omega
    have he1 : 1 ≤ e := by omega
    have hDgt := OddPerfectNumber.k_one_q2_five_q3_twentynine_D_gt_15_v6
      m a b c e D p q4 sigma hfac hsigma hrel hp hp_eq hq4gt ha hb hc he1
    have hcases := OddPerfectNumber.k_one_q2_five_q3_twentynine_small_D_cases_canonical_v7
      D p q4 hDgt hDlt hDodd hp hp_eq hq4gt hDsupport
    rcases hcases with h27 | hrest
    · exact OddPerfectNumber.k_one_q2_five_q3_twentynine_D27_absurd_v1
        m d sigma D p q4 a b c e hfac hsigma hrel h27 hp hp_eq hq4prime hq4gt
        ha hb hc he hsig hddvd hm0 hglobal hsupport
    · rcases hrest with h31 | hrest
      · exact OddPerfectNumber.k_one_q2_five_q3_twentynine_D31_absurd_v2
          m a b c e D p q4 sigma hsigma hrel h31 hp_eq hp hDsupport hq4prime
      · rcases hrest with h37 | h45
        · exact OddPerfectNumber.k_one_q2_five_q3_twentynine_D37_absurd_v3
            m d D p q4 sigma a b c e hsigma hrel h37 hp_eq hp (by omega)
            hm0 hsig hglobal hddvd hsupport hDsupport hq4prime
        · exact OddPerfectNumber.k_one_q2_five_q3_twentynine_D45_canonical_absurd_v2
            m a b c e D p q4 sigma hfac hsigma hrel h45 hp_eq hq4prime
            hq4gt ha hb hc he
