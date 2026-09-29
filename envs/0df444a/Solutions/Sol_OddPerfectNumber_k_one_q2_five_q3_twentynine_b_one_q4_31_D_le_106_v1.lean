-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_q4_31_D_le_106_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T06:09:18.644074+00:00
-- url     : https://prove2.me/submissions/20deb149-0426-4a94-8894-b68a6323e10b

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

open OddPerfectNumber

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4eq : q4 = 31)
    (hb1 : b = 1) (ha : 4 ≤ a) (hc : 2 ≤ c) (he : 1 ≤ e) :
    D < 107 := by
  subst hq4eq
  have h8 : 8 ≤ 2 * a := by omega
  have h2c : 1 ≤ 2 * c := by omega
  have h2e : 1 ≤ 2 * e := by omega
  have hb2 : 2 * b = 2 := by omega
  have hS5 : ∑ i ∈ Finset.range (2*b + 1), 5 ^ i = 31 := by
    have : 2 * b + 1 = 3 := by omega
    rw [this]; decide
  have h52b : 5 ^ (2*b) = 25 := by
    rw [hb2]; norm_num
  let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S29 := ∑ i ∈ Finset.range (2*c + 1), 29 ^ i
  let Sq := ∑ i ∈ Finset.range (2*e + 1), 31 ^ i
  have hu3 := OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a)
    (by norm_num) (by norm_num) (by norm_num)
  have hu29 := OddPerfectNumber.geom_sum_cross_lt_of_le 29 29 (2*c)
    (by norm_num) (by norm_num) (by norm_num)
  have huq := OddPerfectNumber.geom_sum_cross_lt_of_le 31 31 (2*e)
    (by norm_num) (by rfl) (by norm_num)
  have hu := Nat.mul_lt_mul_of_lt_of_lt
    (Nat.mul_lt_mul_of_lt_of_lt hu3 hu29) huq
  have hmul31 : (((2*S3) * (28*S29) * ((31-1)*Sq)) * 31) <
      (((3*3^(2*a)) * (29*29^(2*c)) * (31*31^(2*e))) * 31) := by
    gcongr
  have hupper : 42000 * sigma < 83607 * m ^ 2 := by
    calc
      42000 * sigma =
          25 * (((2*S3) * (28*S29) * ((31-1)*Sq)) * 31) := by
            rw [hsigma, hS5]
            dsimp [S3, S29, Sq]
            ring
      _ < 25 * (((3*3^(2*a)) * (29*29^(2*c)) * (31*31^(2*e))) * 31) := by
            gcongr
      _ = 83607 * m ^ 2 := by
        rw [hfac, h52b]
        ring
  have hcoef : 42000 * p < 83607 * D := by
    have hmpos : 0 < m ^ 2 := by rw [hfac]; positivity
    have hDpos : 0 < D := by
      have h2 := hp.two_le
      omega
    have hineq : 42000 * p * m ^ 2 < 83607 * D * m ^ 2 := by
      calc
        42000 * p * m ^ 2 =
            42000 * (p * m ^ 2) := by ring
        _ = 42000 * (D * sigma) := by rw [hrel]
        _ = D * (42000 * sigma) := by ring
        _ < D * (83607 * m ^ 2) :=
          (Nat.mul_lt_mul_left hDpos).2 hupper
        _ = 83607 * D * m ^ 2 := by ring
    exact Nat.lt_of_mul_lt_mul_right (by simpa [Nat.mul_assoc] using hineq)
  rw [hp_eq] at hcoef
  omega
