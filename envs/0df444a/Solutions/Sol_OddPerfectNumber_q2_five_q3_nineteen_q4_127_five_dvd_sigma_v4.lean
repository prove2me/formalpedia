-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_127_five_dvd_sigma_v4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T02:05:08.776534+00:00
-- url     : https://prove2.me/submissions/ab838590-b552-42b0-ae55-1fbf728ee6fb

import Mathlib
import Theorems.Thm_OddPerfectNumber_nat_prime_pow_dvd_of_dvd_mul_right

theorem solution (p m d sigma : Nat)
    (hp : p.Prime)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsigma : sigma = p * d)
    (hD : (p + 1) / 2 < 185)
    (hpow : 5 ^ 6 ∣ m ^ 2) :
    5 ∣ sigma := by
  have hp2 : 2 ≤ p := hp.two_le
  have hDpos : 0 < (p + 1) / 2 := by omega
  have hpow' : 5 ^ 6 ∣ ((p + 1) / 2) * d := by
    rw [← hprod]
    exact hpow
  have h5d : 5 ∣ d := by
    by_contra hnot
    have hDpow : 5 ^ 6 ∣ (p + 1) / 2 := by
      exact OddPerfectNumber.nat_prime_pow_dvd_of_dvd_mul_right
        5 ((p + 1) / 2) d 6 (by norm_num) hnot hpow'
    have hle : 5 ^ 6 ≤ (p + 1) / 2 :=
      Nat.le_of_dvd hDpos hDpow
    norm_num at hle
    have hsmall : 15625 < 185 := lt_of_le_of_lt hle hD
    norm_num at hsmall
  rw [hsigma]
  exact dvd_mul_of_dvd_right h5d p
