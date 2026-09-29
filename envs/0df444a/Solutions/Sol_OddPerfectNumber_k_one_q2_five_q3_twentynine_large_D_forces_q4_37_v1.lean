-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_forces_q4_37_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T10:37:31.243846+00:00
-- url     : https://prove2.me/submissions/e390cf75-5934-42be-aa50-f94f3134ecd5

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_le_43_v4
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_cases_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_31_or_43_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_41_canonical_absurd_v1

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 75 ≤ D)
    (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4)
    (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) : q4 = 37 := by
  have hq4le := OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_le_43_v4
    m a b c e D p q4 sigma hfac hsigma hrel hDlow hp hp_eq hq4prime hq4gt
    ha hb hc he
  have hcases := OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_cases_v1
    q4 hq4prime hq4gt hq4le
  rcases hcases with h31 | h37 | h41 | h43
  · exact False.elim (OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_31_or_43_absurd_v1
      m a b c e D p q4 sigma hfac hsigma hrel hDlow hDodd hp hp_eq hq4prime hq4gt
      hDsupport (Or.inl h31) ha hb hc he)
  · exact h37
  · exact False.elim (OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_41_canonical_absurd_v1
      m a b c e D p q4 sigma hfac hsigma hrel hDlow hDodd hp hp_eq hq4prime h41
      hDsupport ha hb hc he)
  · exact False.elim (OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_31_or_43_absurd_v1
      m a b c e D p q4 sigma hfac hsigma hrel hDlow hDodd hp hp_eq hq4prime hq4gt
      hDsupport (Or.inr h43) ha hb hc he)
