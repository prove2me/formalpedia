-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_q4_six_cases
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T15:19:07.121266+00:00
-- url     : https://prove2.me/submissions/755d94f8-bd17-448f-a818-27d8e366ff8f

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_q4_le_113_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_q4_gt_89
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_q4_prime_cases

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlow : 225 ≤ D) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    q4 = 97 ∨ q4 = 101 ∨ q4 = 103 ∨ q4 = 107 ∨ q4 = 109 ∨ q4 = 113 := by
  have hq4le : q4 ≤ 113 := by
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_q4_le_113_v2
      m a b c e D p q4 sigma hfac hsigma hrel hDlow hp_eq hq4prime hq4gt
  have hq4gt89 : 89 < q4 := by
    by_contra hbad
    have hle : q4 ≤ 89 := by omega
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_q4_gt_89
      m a b c e D p q4 sigma hfac hsigma hrel hDlow hp_eq hq4prime hq4gt
      ha hb hc he hle
  have hcases := OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_q4_prime_cases
    q4 hq4prime hq4gt hq4le
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals omega
