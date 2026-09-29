-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D45_D69_q4_ranges_v4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T00:05:49.815313+00:00
-- url     : https://prove2.me/submissions/5b777a6d-2b1f-432c-8f04-42f3bab34b20

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDcases : D = 45 ∨ D = 69) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hDq : D < q4)
    (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e) :
    (D = 45 ∧ 46 ≤ q4 ∧ q4 ≤ 112) ∨
      (D = 69 ∧ 70 ≤ q4 ∧ q4 ≤ 78) := by
  let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S23 := ∑ i ∈ Finset.range (2*c + 1), 23 ^ i
  let Sq := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have hq4pos : 0 < q4 := hq4prime.pos
  have hu3 := OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a) (by norm_num) (by norm_num) (by norm_num)
  have hu5 := OddPerfectNumber.geom_sum_cross_lt_of_le 5 5 (2*b) (by norm_num) (by norm_num) (by norm_num)
  have hu23 := OddPerfectNumber.geom_sum_cross_lt_of_le 23 23 (2*c) (by norm_num) (by norm_num) (by norm_num)
  have huq := OddPerfectNumber.geom_sum_cross_lt_of_le q4 q4 (2*e) (by omega) (by rfl) hq4prime
  have hu := Nat.mul_lt_mul_of_lt_of_lt
    (Nat.mul_lt_mul_of_lt_of_lt hu3 hu5)
    (Nat.mul_lt_mul_of_lt_of_lt hu23 huq)
  have hupper : 176 * (q4 - 1) * sigma < 345 * q4 * m^2 := by
    calc
      176 * (q4 - 1) * sigma = (2*S3)*(4*S5)*(22*S23)*((q4-1)*Sq) := by rw [hsigma]; dsimp [S3,S5,S23,Sq]; ring
      _ < (3*3^(2*a))*(5*5^(2*b))*((23*23^(2*c))*(q4*q4^(2*e))) := by
        simpa [S3,S5,S23,Sq, Nat.mul_assoc] using hu
      _ = 345*q4*m^2 := by rw [hfac]; ring
  have hcoef : 176 * (q4 - 1) * p < 345 * q4 * D := by
    have hmpos : 0 < m^2 := by rw [hfac]; positivity
    have hDpos : 0 < D := by
      rcases hDcases with h45 | h69 <;> omega
    have hineq : 176 * (q4 - 1) * p * m^2 < 345 * q4 * D * m^2 := by
      calc
        176 * (q4 - 1) * p * m^2 = 176 * (q4 - 1) * (p*m^2) := by ring
        _ = 176 * (q4 - 1) * (D*sigma) := by rw [hrel]
        _ = D * (176 * (q4 - 1) * sigma) := by ring
        _ < D * (345*q4*m^2) := (Nat.mul_lt_mul_left hDpos).2 hupper
        _ = 345*q4*D*m^2 := by ring
    exact Nat.lt_of_mul_lt_mul_right (by simpa [Nat.mul_assoc] using hineq)
  rcases hDcases with h45 | h69
  · subst D
    have hlow : 46 ≤ q4 := by omega
    have hpval : p = 89 := by omega
    rw [hpval] at hcoef
    norm_num [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at hcoef
    have hhigh : q4 ≤ 112 := by omega
    exact Or.inl ⟨rfl, hlow, hhigh⟩
  · subst D
    have hlow : 70 ≤ q4 := by omega
    have hpval : p = 137 := by omega
    rw [hpval] at hcoef
    norm_num [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at hcoef
    have hhigh : q4 ≤ 78 := by omega
    exact Or.inr ⟨rfl, hlow, hhigh⟩
