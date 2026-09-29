-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_q4_31_e_one_331_dvd_sigma_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T02:46:40.096677+00:00
-- url     : https://prove2.me/submissions/20899320-8840-43b4-a04f-d5017619a66e

import Mathlib

-- EXPONENT CONVENTION: full exponents; the 31-component has full exponent 2 (e = 1).
-- S(31,2) = 993 = 331 * 3, so 331 divides any sigma containing this factor.
theorem solution (a b c sigma : Nat)
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range 3, 31 ^ i)) :
    331 ∣ sigma := by
  have h3 : (∑ i ∈ Finset.range 3, 31 ^ i) = 993 := by
    norm_num [Finset.sum_range_succ]
  rw [h3] at hsigma
  exact ⟨(∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
    (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
    (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * 3, by rw [hsigma]; ring⟩
