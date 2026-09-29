-- Prove2me | solution 1 for OddPerfectNumber.k_one_p5_no_local_sigma_source_3_23_53
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T04:32:03.315458+00:00
-- url     : https://prove2.me/submissions/8b7fe5ed-9bd0-4d05-9a1e-781fd491d8e2

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate
import Theorems.Thm_OddPerfectNumber_prime_not_dvd_own_sigma_prime_pow

theorem solution (sigma a b c e : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), 53 ^ i))
    (hdiv : 5 ∣ sigma)
    (h3 : ¬ orderOf (3 : ZMod 5) ∣ 2 * a + 1)
    (h23 : ¬ orderOf (23 : ZMod 5) ∣ 2 * c + 1)
    (h53 : ¬ orderOf (53 : ZMod 5) ∣ 2 * e + 1) :
    False := by
  have hno3 := OddPerfectNumber.geom_sum_not_dvd_of_order_certificate (p := 5) (q := 3) (e := a) h3
  have hno23 := OddPerfectNumber.geom_sum_not_dvd_of_order_certificate (p := 5) (q := 23) (e := c) h23
  have hno53 := OddPerfectNumber.geom_sum_not_dvd_of_order_certificate (p := 5) (q := 53) (e := e) h53
  have hno5 : ¬ 5 ∣ ∑ i ∈ Finset.range (2 * b + 1), 5 ^ i :=
    OddPerfectNumber.prime_not_dvd_own_sigma_prime_pow 5 (2 * b) (by norm_num)
  have hp : Nat.Prime 5 := by norm_num
  have h := hdiv
  rw [hsigma] at h
  rcases hp.dvd_mul.mp h with hleft | h53div
  · rcases hp.dvd_mul.mp hleft with hleft' | h23div
    · rcases hp.dvd_mul.mp hleft' with h3div | h5div
      · exact hno3 h3div
      · exact hno5 h5div
    · exact hno23 h23div
  · exact hno53 h53div
