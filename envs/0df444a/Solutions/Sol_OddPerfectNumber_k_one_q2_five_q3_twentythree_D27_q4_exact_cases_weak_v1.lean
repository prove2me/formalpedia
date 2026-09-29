-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_q4_exact_cases_weak_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T10:27:57.694355+00:00
-- url     : https://prove2.me/submissions/46c87c9d-1406-4eb0-aa4f-0ac9d457299d

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_ge_691_half_floors_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_le_717
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_window_cases

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents (weak floors 4,3,2,1).
theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 27) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 23 < q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    q4 = 691 ∨ q4 = 701 ∨ q4 = 709 := by
  have hlo := OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_q4_ge_691_half_floors_v2
    m a b c e D p q4 sigma hfac hsigma hrel hD hp_eq hq4prime hq4gt ha hb hc he
  have hhi := OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_q4_le_717
    m a b c e D p q4 sigma hfac hsigma hrel hD hp_eq hq4prime hq4gt
  exact OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_q4_window_cases
    q4 hq4prime hlo hhi
