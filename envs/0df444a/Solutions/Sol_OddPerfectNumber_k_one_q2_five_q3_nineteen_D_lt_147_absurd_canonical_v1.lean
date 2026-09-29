-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_D_lt_147_absurd_canonical_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T19:53:55.586001+00:00
-- url     : https://prove2.me/submissions/ea125441-ac4f-4e02-8cf8-0779e460cda2

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_le_D_D_le_141_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_survivors
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_q4_ranges_v6
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_canonical_absurd_v4

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlt : D < 147) (hDodd : Odd D) (hp : p.Prime)
    (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  have hD225 : D < 225 := by omega
  by_cases hq4le : q4 ≤ D
  · by_cases hD141 : D ≤ 141
    · exact OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_le_D_D_le_141_absurd_v1
        m a b c e D p q4 sigma hfac hsigma hrel (by omega) hDodd hD141 hp hp_eq
        hq4prime hq4gt hq4le ha hb hc he
    · have hD142 : 142 ≤ D := by omega
      interval_cases D <;> norm_num at hDodd <;>
        norm_num [hp_eq] at hp <;> omega
  · have hDq : D < q4 := by omega
    have hcases := OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_survivors
      m (2*a) (2*b) (2*c) (2*e) D p q4 sigma
      (by simpa using hfac) (by simpa using hsigma) hrel hD225 hDodd hp hp_eq
      hq4prime hq4gt hDq hDsupport (by omega) (by omega) (by omega) (by omega)
    have hqranges := OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_q4_ranges_v6
      m a b c e D p q4 sigma hfac hsigma hrel hcases hp_eq hq4prime hDq
      ha hb hc he
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_canonical_absurd_v4
      m a b c e D p q4 sigma hfac hsigma hrel hD225 hDodd hp hp_eq hq4prime
      hq4gt hDq hDsupport ha hb hc he hqranges
