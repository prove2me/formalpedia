-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_D37_external_127_sigma_lift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T08:12:16.353533+00:00
-- url     : https://prove2.me/submissions/7fa0291a-a23a-4e88-98f5-d71e9cd3997b

import Mathlib

theorem solution (sigma a b c e : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), 37 ^ i))
    (hlocal : 127 ∣ ∑ i ∈ Finset.range (2 * e + 1), 37 ^ i) :
    127 ∣ sigma := by
  rw [hsigma]
  exact dvd_mul_of_dvd_right hlocal _
