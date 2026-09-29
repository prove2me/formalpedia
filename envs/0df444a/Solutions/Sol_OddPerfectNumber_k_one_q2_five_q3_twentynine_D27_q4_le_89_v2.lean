-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D27_q4_le_89_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T08:47:39.542663+00:00
-- url     : https://prove2.me/submissions/8817cc3e-a8e5-4ac4-a9e9-1645281166fe

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
    (hD : D = 27) (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    q4 ≤ 89 := by
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
  have hp53 : p = 53 := by omega
  rw [hD, hp53] at hcoef
  norm_num at hcoef
  have hcoef' : 11872 * (q4 - 1) < 11745 * q4 := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcoef
  by_contra hq4le
  have hq4ge90 : 90 ≤ q4 := by omega
  have hq4ne90 : q4 ≠ 90 := by
    intro h
    subst q4
    norm_num at hq4prime
  have hq4ne91 : q4 ≠ 91 := by
    intro h
    subst q4
    norm_num at hq4prime
  have hq4ne92 : q4 ≠ 92 := by
    intro h
    subst q4
    norm_num at hq4prime
  have hq4ne93 : q4 ≠ 93 := by
    intro h
    subst q4
    norm_num at hq4prime
  have hq4ge : 94 ≤ q4 := by omega
  have hlin : 127 * q4 < 11872 := by omega
  omega
