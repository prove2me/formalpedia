-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_q4_ranges_v6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T01:25:16.506988+00:00
-- url     : https://prove2.me/submissions/85013d63-e0e9-4b53-b8a0-b1c3a495bd0a

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_four
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDcases : D = 57 ∨ D = 75 ∨ D = 135)
    (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hDq : D < q4) (ha : 4 ≤ a) (hb : 3 ≤ b)
    (hc : 2 ≤ c) (he : 1 ≤ e) :
    (D = 57 ∧ 580 ≤ q4 ∧ q4 ≤ 602) ∨
      (D = 75 ∧ 261 ≤ q4 ∧ q4 ≤ 264) ∨
      (D = 135 ∧ 146 ≤ q4 ∧ q4 ≤ 148) := by
  let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S19 := ∑ i ∈ Finset.range (2*c + 1), 19 ^ i
  let Sq := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have hq4pos : 0 < q4 := hq4prime.pos
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have h19 := OddPerfectNumber.geom_ratio_lower_nineteen_ge_four (2*c) (by omega)
  have hbase :
      (9841 * 19531 * 137561) *
          (3^(2*a) * 5^(2*b) * 19^(2*c)) ≤
        (6561 * 15625 * 130321) * (S3 * S5 * S19) := by
    have hmul35 := Nat.mul_le_mul h3 h5
    have hmul := Nat.mul_le_mul hmul35 h19
    simpa [S3, S5, S19, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  have hlast := OddPerfectNumber.geom_sum_last_three_terms_le q4 (2*e) (by omega)
  have hpow1 : q4^(2*e) = q4^2 * q4^(2*e-2) := by
    calc
      q4^(2*e) = q4^((2*e-2)+2) := by congr 1 <;> omega
      _ = q4^2 * q4^(2*e-2) := by rw [pow_add]; ring
  have hpow2 : q4^(2*e-1) = q4 * q4^(2*e-2) := by
    calc
      q4^(2*e-1) = q4^((2*e-2)+1) := by congr 1 <;> omega
      _ = q4 * q4^(2*e-2) := by rw [pow_add]; ring
  have hqpoly :
      (q4^2 + q4 + 1) * q4^(2*e-2) ≤ Sq := by
    dsimp [Sq] at hlast ⊢
    calc
      (q4^2 + q4 + 1) * q4^(2*e-2) =
          q4^2 * q4^(2*e-2) + q4 * q4^(2*e-2) + q4^(2*e-2) := by ring
      _ = q4^2 * q4^(2*e-2) + q4^1 * q4^(2*e-2) + q4^(2*e-2) := by norm_num
      _ = q4^(2 + (2*e-2)) + q4^(1 + (2*e-2)) + q4^(2*e-2) := by
        rw [← pow_add, ← pow_add]
      _ = q4^(2*e) + q4^(2*e-1) + q4^(2*e-2) := by
        have he1 : 2 + (2*e - 2) = 2*e := by omega
        have he2 : 1 + (2*e - 2) = 2*e - 1 := by omega
        rw [he1, he2]
      _ ≤ ∑ i ∈ Finset.range (2*e + 1), q4^i := hlast
  have hpoly :
      (9841 * 19531 * 137561) * D * (q4^2 + q4 + 1) ≤
        (6561 * 15625 * 130321) * p * q4^2 := by
    have hmul := Nat.mul_le_mul hbase hqpoly
    have hmulD := Nat.mul_le_mul_left D hmul
    have hfac' : m^2 =
        (3^(2*a) * 5^(2*b) * 19^(2*c)) *
          (q4^2 * q4^(2*e-2)) := by
      rw [hfac, hpow1]
    have hmpos : 0 < m^2 := by rw [hfac]; positivity
    have hstep :
        (9841 * 19531 * 137561) * D *
            ((3^(2*a) * 5^(2*b) * 19^(2*c)) *
              ((q4^2 + q4 + 1) * q4^(2*e-2))) ≤
          (6561 * 15625 * 130321) * (D * sigma) := by
      calc
        _ = D * ((9841 * 19531 * 137561) *
            ((3^(2*a) * 5^(2*b) * 19^(2*c)) *
              ((q4^2 + q4 + 1) * q4^(2*e-2)))) := by ring
        _ ≤ D * ((6561 * 15625 * 130321) * (S3*S5*S19) * Sq) := by
          simpa [S3, S5, S19, Sq, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmulD
        _ = (6561 * 15625 * 130321) * (D * sigma) := by rw [hsigma]; ring
    rw [hrel, hfac'] at hstep
    let X := (3^(2*a) * 5^(2*b) * 19^(2*c)) * q4^(2*e-2)
    have hstep' :
        ((9841 * 19531 * 137561) * D * (q4^2 + q4 + 1)) * X ≤
          ((6561 * 15625 * 130321) * p * q4^2) * X := by
      dsimp [X]
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hstep
    apply Nat.le_of_mul_le_mul_right (by simpa [Nat.mul_assoc] using hstep')
    have hXpos : 0 < X := by
      dsimp [X]
      positivity
    exact hXpos
  have hu3 := OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a) (by norm_num) (by norm_num) (by norm_num)
  have hu5 := OddPerfectNumber.geom_sum_cross_lt_of_le 5 5 (2*b) (by norm_num) (by norm_num) (by norm_num)
  have hu19 := OddPerfectNumber.geom_sum_cross_lt_of_le 19 19 (2*c) (by norm_num) (by norm_num) (by norm_num)
  have huq := OddPerfectNumber.geom_sum_cross_lt_of_le q4 q4 (2*e) (by omega) (by rfl) hq4prime
  have hu := Nat.mul_lt_mul_of_lt_of_lt
    (Nat.mul_lt_mul_of_lt_of_lt hu3 hu5)
    (Nat.mul_lt_mul_of_lt_of_lt hu19 huq)
  have hupper : 144 * (q4 - 1) * sigma < 285 * q4 * m^2 := by
    calc
      144 * (q4 - 1) * sigma = (2*S3)*(4*S5)*(18*S19)*((q4-1)*Sq) := by rw [hsigma]; dsimp [S3,S5,S19,Sq]; ring
      _ < (3*3^(2*a))*(5*5^(2*b))*((19*19^(2*c))*(q4*q4^(2*e))) := by
        simpa [S3,S5,S19,Sq, Nat.mul_assoc] using hu
      _ = 285*q4*m^2 := by rw [hfac]; ring
  have hcoef : 144 * (q4 - 1) * p < 285 * q4 * D := by
    have hmpos : 0 < m^2 := by rw [hfac]; positivity
    have hDpos : 0 < D := by
      rcases hDcases with h57 | h75 | h135 <;> omega
    have hineqU :
        144 * (q4 - 1) * p * m^2 < 285 * q4 * D * m^2 := by
      calc
        144 * (q4 - 1) * p * m^2 =
            144 * (q4 - 1) * (p * m^2) := by ring
        _ = 144 * (q4 - 1) * (D * sigma) := by rw [hrel]
        _ = D * (144 * (q4 - 1) * sigma) := by ring
        _ < D * (285 * q4 * m^2) := (Nat.mul_lt_mul_left hDpos).2 hupper
        _ = 285 * q4 * D * m^2 := by ring
    exact Nat.lt_of_mul_lt_mul_right (by simpa [Nat.mul_assoc] using hineqU)
  rcases hDcases with h57 | h75 | h135
  · subst D
    have hpval : p = 113 := by omega
    rw [hpval] at hpoly hcoef
    norm_num at hpoly hcoef
    ring_nf at hpoly hcoef
    have hlow : 580 ≤ q4 := by
      by_contra hbad
      have hqle : q4 ≤ 579 := by omega
      have hq2 : q4^2 ≤ 579^2 := Nat.pow_le_pow_left hqle 2
      nlinarith only [hpoly, hq2]
    have hhigh : q4 ≤ 602 := by
      by_contra hbad
      have hqge : 603 ≤ q4 := by omega
      have hq2 : 603^2 ≤ q4^2 := Nat.pow_le_pow_left hqge 2
      omega
    exact Or.inl ⟨rfl, hlow, hhigh⟩
  · subst D
    have hpval : p = 149 := by omega
    rw [hpval] at hpoly hcoef
    norm_num at hpoly hcoef
    ring_nf at hpoly hcoef
    have hlow : 261 ≤ q4 := by
      by_contra hbad
      have hqle : q4 ≤ 260 := by omega
      have hq2 : q4^2 ≤ 260^2 := Nat.pow_le_pow_left hqle 2
      nlinarith only [hpoly, hq2]
    have hhigh : q4 ≤ 264 := by
      by_contra hbad
      have hqge : 265 ≤ q4 := by omega
      have hq2 : 265^2 ≤ q4^2 := Nat.pow_le_pow_left hqge 2
      omega
    exact Or.inr (Or.inl ⟨rfl, hlow, hhigh⟩)
  · subst D
    have hpval : p = 269 := by omega
    rw [hpval] at hpoly hcoef
    norm_num at hpoly hcoef
    ring_nf at hpoly hcoef
    have hlow : 146 ≤ q4 := by
      by_contra hbad
      have hqle : q4 ≤ 145 := by omega
      have hq2 : q4^2 ≤ 145^2 := Nat.pow_le_pow_left hqle 2
      nlinarith only [hpoly, hq2]
    have hhigh : q4 ≤ 148 := by
      by_contra hbad
      have hqge : 149 ≤ q4 := by omega
      have hq2 : 149^2 ≤ q4^2 := Nat.pow_le_pow_left hqge 2
      omega
    exact Or.inr (Or.inr ⟨rfl, hlow, hhigh⟩)
