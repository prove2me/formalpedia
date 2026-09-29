-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_absurd_half_floors_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T11:49:15.750514+00:00
-- url     : https://prove2.me/submissions/f78cb273-d655-4ac4-b6c1-92b83372b3c1

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_ge_691_half_floors_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_le_717
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_window_cases
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_sigma_div_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_small_D_absurd

-- EXPONENT CONVENTION: a,b,c,e are half exponents.
theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 27) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 23 < q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    False := by
  have hlo := OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_q4_ge_691_half_floors_v2
    m a b c e D p q4 sigma hfac hsigma hrel hD hp_eq hq4prime hq4gt ha hb hc he
  have hhi := OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_q4_le_717
    m a b c e D p q4 sigma hfac hsigma hrel hD hp_eq hq4prime hq4gt
  have hcases := OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_q4_window_cases
    q4 hq4prime hlo hhi
  have hdiv := OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_sigma_div_v1
    m D p sigma hrel hD hp_eq
  exact OddPerfectNumber.k_one_q2_five_q3_twentythree_small_D_absurd
    sigma a b c e q4 hsigma hdiv hcases
