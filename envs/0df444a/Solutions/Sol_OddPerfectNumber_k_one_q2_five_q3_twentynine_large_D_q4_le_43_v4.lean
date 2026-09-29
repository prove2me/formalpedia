-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_le_43_v4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T05:07:40.542845+00:00
-- url     : https://prove2.me/submissions/9777fb1d-c273-478d-82a0-91b376a4b0d2

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlow : 75 ≤ D) (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) :
    q4 ≤ 43 := by
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
  rw [hp_eq] at hcoef
  by_contra hq4le
  have hq4ge : 44 ≤ q4 := by omega
  have hq4ge47 : 47 ≤ q4 := by
    by_contra h
    have hq4le46 : q4 ≤ 46 := by omega
    interval_cases q4 <;> norm_num at hq4prime <;> omega
  have hratio : 46 * q4 ≤ 47 * (q4 - 1) := by omega
  have hlin : 47 * 435 * D ≤ 224 * 46 * (2 * D - 1) := by
    omega
  have hlinq : 47 * 435 * q4 * D ≤
      224 * 46 * q4 * (2 * D - 1) := by
    have := Nat.mul_le_mul_right q4 hlin
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
  have hleft : 224 * 46 * q4 * (2 * D - 1) ≤
      47 * 224 * (q4 - 1) * (2 * D - 1) := by
    have := Nat.mul_le_mul_right (224 * (2 * D - 1)) hratio
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
  have hright : 47 * 224 * (q4 - 1) * (2 * D - 1) <
      47 * 435 * q4 * D := by
    have h := (Nat.mul_lt_mul_left (by norm_num : 0 < 47)).2 hcoef
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have : 47 * 435 * q4 * D < 47 * 435 * q4 * D :=
    lt_of_le_of_lt hlinq (lt_of_le_of_lt hleft hright)
  omega
