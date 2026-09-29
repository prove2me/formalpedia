-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D31_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T02:55:41.761691+00:00
-- url     : https://prove2.me/submissions/0c19db01-026f-4516-8661-637cdde5291d

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order
import Theorems.Thm_OddPerfectNumber_even_orders_mod_61_q3_twentynine
import Theorems.Thm_OddPerfectNumber_even_order_31_mod_61

theorem solution (m a b c e D p q4 sigma : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hD : D = 31)
    (hp_eq : p = 2 * D - 1) (hp : p.Prime)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4)
    (hq4prime : q4.Prime) : False := by
  subst D
  norm_num at hp_eq
  subst p
  have h31prime : Nat.Prime 31 := by norm_num
  have h61prime : Nat.Prime 61 := by norm_num
  have hq4eq : q4 = 31 := by
    have hcase := hDsupport 31 h31prime (by exact dvd_refl 31)
    rcases hcase with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · exact h.symm
  subst q4
  have h61left : 61 ∣ 31 * sigma := by
    rw [hrel]
    simpa [Nat.mul_comm] using (dvd_mul_left 61 (m ^ 2))
  have h61sigma : 61 ∣ sigma := by
    rcases h61prime.dvd_mul.mp h61left with hbad | hs
    · norm_num at hbad
    · exact hs
  rw [hsigma] at h61sigma
  have h3 : ¬ 61 ∣ (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) :=
    OddPerfectNumber.geom_sum_not_dvd_of_even_order
      (OddPerfectNumber.even_orders_mod_61_q3_twentynine.1)
  have h5 : ¬ 61 ∣ (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) :=
    OddPerfectNumber.geom_sum_not_dvd_of_even_order
      (OddPerfectNumber.even_orders_mod_61_q3_twentynine.2.1)
  have h29 : ¬ 61 ∣ (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) :=
    OddPerfectNumber.geom_sum_not_dvd_of_even_order
      (OddPerfectNumber.even_orders_mod_61_q3_twentynine.2.2)
  have h31 : ¬ 61 ∣ (∑ i ∈ Finset.range (2*e + 1), 31 ^ i) :=
    OddPerfectNumber.geom_sum_not_dvd_of_even_order
      (OddPerfectNumber.even_order_31_mod_61)
  rcases h61prime.dvd_mul.mp h61sigma with hleft | h31s
  · rcases h61prime.dvd_mul.mp hleft with hleft2 | h29s
    · rcases h61prime.dvd_mul.mp hleft2 with h3s | h5s
      · exact h3 h3s
      · exact h5 h5s
    · exact h29 h29s
  · exact h31 h31s
