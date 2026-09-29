-- Prove2me | solution 1 for OddPerfectNumber.k_one_p113_no_local_sigma_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T04:25:24.984857+00:00
-- url     : https://prove2.me/submissions/a4d2aab0-72e7-417c-8396-aca3773a5aec

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate

theorem solution (sigma a b c e : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), 587 ^ i))
    (hdiv : 113 ∣ sigma)
    (h3 : ¬ orderOf (3 : ZMod 113) ∣ 2 * a + 1)
    (h5 : ¬ orderOf (5 : ZMod 113) ∣ 2 * b + 1)
    (h19 : ¬ orderOf (19 : ZMod 113) ∣ 2 * c + 1)
    (h587 : ¬ orderOf (587 : ZMod 113) ∣ 2 * e + 1) :
    False := by
  have hno3 := OddPerfectNumber.geom_sum_not_dvd_of_order_certificate (p := 113) (q := 3) (e := a) h3
  have hno5 := OddPerfectNumber.geom_sum_not_dvd_of_order_certificate (p := 113) (q := 5) (e := b) h5
  have hno19 := OddPerfectNumber.geom_sum_not_dvd_of_order_certificate (p := 113) (q := 19) (e := c) h19
  have hno587 := OddPerfectNumber.geom_sum_not_dvd_of_order_certificate (p := 113) (q := 587) (e := e) h587
  have hp : Nat.Prime 113 := by norm_num
  have h := hdiv
  rw [hsigma] at h
  rcases hp.dvd_mul.mp h with hleft | h587div
  · rcases hp.dvd_mul.mp hleft with hleft' | h19div
    · rcases hp.dvd_mul.mp hleft' with h3div | h5div
      · exact hno3 h3div
      · exact hno5 h5div
    · exact hno19 h19div
  · exact hno587 h587div
