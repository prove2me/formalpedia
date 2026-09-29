-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_D_le_481_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T08:33:04.973965+00:00
-- url     : https://prove2.me/submissions/3a907c8e-a78f-4d8b-b781-b06c2dac15ae

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDpos : 0 < D)
    (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4ge : 53 ≤ q4) : D ≤ 481 := by
  have hu3 := OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a)
    (by norm_num) (by norm_num) (by norm_num)
  have hu5 := OddPerfectNumber.geom_sum_cross_lt_of_le 5 5 (2*b)
    (by norm_num) (by norm_num) (by norm_num)
  have hu23 := OddPerfectNumber.geom_sum_cross_lt_of_le 23 23 (2*c)
    (by norm_num) (by norm_num) (by norm_num)
  have huq := OddPerfectNumber.geom_sum_cross_lt_of_le 53 q4 (2*e)
    (by norm_num) hq4ge hq4prime
  have hu := Nat.mul_lt_mul_of_lt_of_lt
    (Nat.mul_lt_mul_of_lt_of_lt hu3 hu5)
    (Nat.mul_lt_mul_of_lt_of_lt hu23 huq)
  have hupper : 9152 * sigma < 18285 * m ^ 2 := by
    calc
      9152 * sigma =
          ((2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
           (4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i))) *
          ((22 * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i)) *
           (52 * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))) := by
        rw [hsigma]
        ring
      _ < ((3 * 3^(2*a)) * (5 * 5^(2*b))) *
          ((23 * 23^(2*c)) * (53 * q4^(2*e))) := by
        simpa using hu
      _ = 18285 * m ^ 2 := by rw [hfac]; ring
  have hineq : (9152 * p) * m ^ 2 < (18285 * D) * m ^ 2 := by
    calc
      (9152 * p) * m ^ 2 = 9152 * (p * m ^ 2) := by ring
      _ = 9152 * (D * sigma) := by rw [hrel]
      _ = D * (9152 * sigma) := by ring
      _ < D * (18285 * m ^ 2) := (Nat.mul_lt_mul_left hDpos).2 hupper
      _ = (18285 * D) * m ^ 2 := by ring
  have hcoef : 9152 * p < 18285 * D := Nat.lt_of_mul_lt_mul_right hineq
  rw [hp_eq] at hcoef
  omega
