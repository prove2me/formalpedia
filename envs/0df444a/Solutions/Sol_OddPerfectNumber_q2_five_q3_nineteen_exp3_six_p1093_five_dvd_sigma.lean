-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_exp3_six_p1093_five_dvd_sigma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T02:07:03.32492+00:00
-- url     : https://prove2.me/submissions/eb3cee56-4cf5-46f5-93c0-d8d09c51bea4

import Mathlib
import Theorems.Thm_OddPerfectNumber_nat_prime_pow_dvd_of_dvd_mul_right

theorem solution (m d sigma : Nat)
    (hprod : m ^ 2 = 547 * d)
    (hsigma : sigma = 1093 * d)
    (hpow : 5 ^ 6 ∣ m ^ 2) :
    5 ∣ sigma := by
  have hpow' : 5 ^ 6 ∣ 547 * d := by
    rw [← hprod]
    exact hpow
  have h5d : 5 ∣ d := by
    by_contra hnot
    have hDpow : 5 ^ 6 ∣ 547 := by
      exact OddPerfectNumber.nat_prime_pow_dvd_of_dvd_mul_right
        5 547 d 6 (by norm_num) hnot hpow'
    have hle : 5 ^ 6 ≤ 547 := Nat.le_of_dvd (by norm_num) hDpow
    norm_num at hle
  rw [hsigma]
  exact dvd_mul_of_dvd_right h5d 1093
