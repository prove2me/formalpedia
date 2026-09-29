-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_middle_D_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T07:55:57.735763+00:00
-- url     : https://prove2.me/submissions/587b711d-4d17-4dfb-bbe1-43d8ef1207a2

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D_lt_147_absurd_canonical_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_middle_q4_le_139_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_middle_q4_gt_D_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_gt_141_self_cases_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_self_cases_abundance_absurd_v2

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlt225 : D < 225)
    (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  by_cases hDlt147 : D < 147
  · exact OddPerfectNumber.k_one_q2_five_q3_nineteen_D_lt_147_absurd_canonical_v1
      m a b c e D p q4 sigma hfac hsigma hrel hDlt147 hDodd hp hp_eq
      hq4prime hq4gt hDsupport ha hb hc he
  have hDlow147 : 147 ≤ D := by omega
  by_cases hq4leD : q4 ≤ D
  · by_cases hq4ge : 142 ≤ q4
    · have hcases := OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_gt_141_self_cases_v1
        m a b c e D p q4 sigma hfac hrel hDlow147 hDlt225 hDodd hp hp_eq
        hq4prime hq4gt hq4ge hq4leD hDsupport
      exact OddPerfectNumber.k_one_q2_five_q3_nineteen_self_cases_abundance_absurd_v2
        m a b c e D p q4 sigma hfac hsigma hrel hcases ha hb hc he hq4prime
    · have hq4le141 : q4 ≤ 141 := by omega
      have hq4le139 : q4 ≤ 139 := by
        by_contra hn
        have hq4eq : q4 = 140 ∨ q4 = 141 := by omega
        rcases hq4eq with rfl | rfl <;> norm_num at hq4prime
      exact OddPerfectNumber.k_one_q2_five_q3_nineteen_middle_q4_le_139_absurd_v1
        m a b c e D p q4 sigma hfac hsigma hrel hDlow147 hDlt225 hp hp_eq
        hq4prime hq4gt hq4le139 ha hb hc he
  · have hq4gtD : D < q4 := by omega
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_middle_q4_gt_D_absurd_v1
      m a b c e D p q4 sigma hfac hsigma hrel hDlow147 hDlt225 hp_eq
      hq4prime hq4gt hq4gtD ha hb hc he
