-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_37_D_le_244_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T08:56:34.783784+00:00
-- url     : https://prove2.me/submissions/16956256-9438-45c3-b615-a36379e936db

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 75 ≤ D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4eq : q4 = 37) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c)
    (he : 1 ≤ e) : D ≤ 244 := by
  let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S29 := ∑ i ∈ Finset.range (2*c + 1), 29 ^ i
  let Sq := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have hu3 := OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a)
    (by norm_num) (by norm_num) (by norm_num)
  have hu5 := OddPerfectNumber.geom_sum_cross_lt_of_le 5 5 (2*b)
    (by norm_num) (by norm_num) (by norm_num)
  have hu29 := OddPerfectNumber.geom_sum_cross_lt_of_le 29 29 (2*c)
    (by norm_num) (by norm_num) (by norm_num)
  have huq := OddPerfectNumber.geom_sum_cross_lt_of_le q4 q4 (2*e)
    (by omega) (by rfl) hq4prime
  have hu := Nat.mul_lt_mul_of_lt_of_lt
    (Nat.mul_lt_mul_of_lt_of_lt hu3 hu5)
    (Nat.mul_lt_mul_of_lt_of_lt hu29 huq)
  have hupper : 224 * (q4 - 1) * sigma < 435 * q4 * m ^ 2 := by
    calc
      224 * (q4 - 1) * sigma =
          (2*S3) * (4*S5) * (28*S29) * ((q4-1)*Sq) := by
            rw [hsigma]
            dsimp [S3, S5, S29, Sq]
            ring
      _ < (3*3^(2*a)) * (5*5^(2*b)) *
          ((29*29^(2*c)) * (q4*q4^(2*e))) := by
            simpa [S3, S5, S29, Sq, Nat.mul_assoc] using hu
      _ = 435 * q4 * m ^ 2 := by
        rw [hfac]
        ring
  have hcoef : 224 * (q4 - 1) * p < 435 * q4 * D := by
    have hmpos : 0 < m ^ 2 := by rw [hfac]; positivity
    have hDpos : 0 < D := by omega
    have hineq : 224 * (q4 - 1) * p * m ^ 2 <
        435 * q4 * D * m ^ 2 := by
      calc
        224 * (q4 - 1) * p * m ^ 2 =
            224 * (q4 - 1) * (p * m ^ 2) := by ring
        _ = 224 * (q4 - 1) * (D * sigma) := by rw [hrel]
        _ = D * (224 * (q4 - 1) * sigma) := by ring
        _ < D * (435 * q4 * m ^ 2) :=
          (Nat.mul_lt_mul_left hDpos).2 hupper
        _ = 435 * q4 * D * m ^ 2 := by ring
    exact Nat.lt_of_mul_lt_mul_right (by simpa [Nat.mul_assoc] using hineq)
  rw [hq4eq, hp_eq] at hcoef
  have hbound := hcoef
  norm_num at hbound
  omega
