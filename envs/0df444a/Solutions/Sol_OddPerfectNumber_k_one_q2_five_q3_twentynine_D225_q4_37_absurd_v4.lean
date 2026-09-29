-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D225_q4_37_absurd_v4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T09:41:28.555503+00:00
-- url     : https://prove2.me/submissions/44b4cec0-828a-4f3c-b84b-5515d6afbcdf

import Mathlib
import Theorems.Thm_OddPerfectNumber_even_orders_mod_449_q3_twentynine
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hD : D = 225)
    (hp_eq : p = 2 * D - 1) (hp : p.Prime) (hq4eq : q4 = 37) : False := by
  have hp449 : p = 449 := by omega
  have hdivmul : 449 ∣ 225 * sigma := by
    rw [← hD, hrel, hp449]
    exact dvd_mul_right 449 (m ^ 2)
  have hdiv : 449 ∣ sigma := by
    rcases (show 449 ∣ 225 ∨ 449 ∣ sigma by
      exact (show Nat.Prime 449 by norm_num).dvd_mul.mp hdivmul) with hbad | hgood
    · norm_num at hbad
    · exact hgood
  have hord := OddPerfectNumber.even_orders_mod_449_q3_twentynine
  have hn3 := OddPerfectNumber.geom_sum_not_dvd_of_even_order (e := a) hord.1
  have hn5 := OddPerfectNumber.geom_sum_not_dvd_of_even_order (e := b) hord.2.1
  have hn29 := OddPerfectNumber.geom_sum_not_dvd_of_even_order (e := c) hord.2.2.1
  have hn37 := OddPerfectNumber.geom_sum_not_dvd_of_even_order (e := e) hord.2.2.2
  rw [hsigma, hq4eq] at hdiv
  have hprod : 449 ∣
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
        ((∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
          ((∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
            (∑ i ∈ Finset.range (2*e + 1), 37 ^ i))) := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hdiv
  rcases (show 449 ∣ (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) ∨
      449 ∣ ((∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
        ((∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
          (∑ i ∈ Finset.range (2*e + 1), 37 ^ i))) by
    exact (show Nat.Prime 449 by norm_num).dvd_mul.mp hprod) with h3 | hrest
  · exact hn3 h3
  have hprod2 : 449 ∣
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
        ((∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
          (∑ i ∈ Finset.range (2*e + 1), 37 ^ i)) := hrest
  rcases (show 449 ∣ (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) ∨
      449 ∣ ((∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
        (∑ i ∈ Finset.range (2*e + 1), 37 ^ i)) by
    exact (show Nat.Prime 449 by norm_num).dvd_mul.mp hprod2) with h5 | hrest2
  · exact hn5 h5
  rcases (show 449 ∣ (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) ∨
      449 ∣ (∑ i ∈ Finset.range (2*e + 1), 37 ^ i) by
    exact (show Nat.Prime 449 by norm_num).dvd_mul.mp hrest2) with h29 | h37
  · exact hn29 h29
  · exact hn37 h37
