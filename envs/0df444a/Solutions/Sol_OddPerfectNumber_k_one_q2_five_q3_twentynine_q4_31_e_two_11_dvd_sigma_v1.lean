-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_q4_31_e_two_11_dvd_sigma_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T02:46:35.212288+00:00
-- url     : https://prove2.me/submissions/0410e9c5-45a5-4193-9b57-0266e190ed7f

import Mathlib

-- EXPONENT CONVENTION: full exponents; the 31-component has full exponent 4 (e = 2).
-- S(31,4) = 954305 = 11 * 86755, so 11 divides any sigma containing this factor.
theorem solution (a b c sigma : Nat)
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range 5, 31 ^ i)) :
    11 ∣ sigma := by
  have h5 : (∑ i ∈ Finset.range 5, 31 ^ i) = 954305 := by
    norm_num [Finset.sum_range_succ]
  rw [h5] at hsigma
  exact ⟨(∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
    (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
    (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * 86755, by rw [hsigma]; ring⟩
