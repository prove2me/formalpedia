-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_D27_nonexception_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T14:38:51.309761+00:00
-- url     : https://prove2.me/submissions/140f5a19-0a30-4681-8f31-77e91c816d14

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D27_source_bridge_v1
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D27_nonexception_even_order_v2
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order

theorem solution (D p sigma m a b c e q4 : Nat)
    (hrel : D * sigma = p * m ^ 2) (hD : D = 27)
    (hp_eq : p = 2 * D - 1)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hcases : q4 = 31 ∨ q4 = 37 ∨ q4 = 41 ∨ q4 = 43 ∨
      q4 = 59 ∨ q4 = 61 ∨ q4 = 67 ∨ q4 = 71 ∨ q4 = 73 ∨
      q4 = 79 ∨ q4 = 83) : False := by
  have hq4even := OddPerfectNumber.q2_five_q3_twentynine_D27_nonexception_even_order_v2
    q4 hcases
  have hq4no : ¬ 53 ∣ ∑ i ∈ Finset.range (2*e + 1), q4 ^ i :=
    OddPerfectNumber.geom_sum_not_dvd_of_even_order
      (p := 53) (q := q4) (e := e) hq4even
  have hq4div := OddPerfectNumber.q2_five_q3_twentynine_D27_source_bridge_v1
    D p sigma m a b c e q4 hrel hD hp_eq hsigma
  exact hq4no hq4div
