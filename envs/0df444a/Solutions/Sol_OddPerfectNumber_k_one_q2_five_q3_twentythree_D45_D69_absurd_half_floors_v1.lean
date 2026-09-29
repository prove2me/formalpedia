-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D45_D69_absurd_half_floors_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T13:44:13.643413+00:00
-- url     : https://prove2.me/submissions/32be6d47-b5cc-4055-b8db-6b21c3b74c3a

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le

-- EXPONENT CONVENTION: half exponents a,b,c,e; full minima 8,6,4,2.
theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDcases : D = 45 ∨ D = 69)
    (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hDq : D < q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S23 := ∑ i ∈ Finset.range (2*c + 1), 23 ^ i
  let Sq := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have hDpos : 0 < D := by rcases hDcases with h | h <;> omega
  have hqpos : 0 < q4 := by omega
  have hmpos : 0 < m^2 := by rw [hfac]; positivity
  have hu3 := OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a)
    (by norm_num) (by norm_num) (by norm_num)
  have hu5 := OddPerfectNumber.geom_sum_cross_lt_of_le 5 5 (2*b)
    (by norm_num) (by norm_num) (by norm_num)
  have hu23 := OddPerfectNumber.geom_sum_cross_lt_of_le 23 23 (2*c)
    (by norm_num) (by norm_num) (by norm_num)
  have huq := OddPerfectNumber.geom_sum_cross_lt_of_le q4 q4 (2*e)
    (by omega) (by rfl) hq4prime
  have hu := Nat.mul_lt_mul_of_lt_of_lt
    (Nat.mul_lt_mul_of_lt_of_lt hu3 hu5) (Nat.mul_lt_mul_of_lt_of_lt hu23 huq)
  have hupper : 176 * (q4-1) * sigma < 345 * q4 * m^2 := by
    calc
      176 * (q4-1) * sigma = (2*S3)*(4*S5)*(22*S23)*((q4-1)*Sq) := by
        rw [hsigma]; dsimp [S3,S5,S23,Sq]; ring
      _ < (3*3^(2*a))*(5*5^(2*b))*((23*23^(2*c))*(q4*q4^(2*e))) := by
        simpa [S3,S5,S23,Sq,Nat.mul_assoc] using hu
      _ = 345*q4*m^2 := by rw [hfac]; ring
  have hcoef : 176 * (q4-1) * p < 345*q4*D := by
    have ht : (176*(q4-1)*p)*m^2 < (345*q4*D)*m^2 := by
      calc
        (176*(q4-1)*p)*m^2 = 176*(q4-1)*(p*m^2) := by ring
        _ = 176*(q4-1)*(D*sigma) := by rw [hrel]
        _ = D*(176*(q4-1)*sigma) := by ring
        _ < D*(345*q4*m^2) := (Nat.mul_lt_mul_left hDpos).2 hupper
        _ = (345*q4*D)*m^2 := by ring
    exact Nat.lt_of_mul_lt_mul_right ht
  obtain ⟨Q, hqQ, hbad⟩ : ∃ Q : Nat, q4 ≤ Q ∧
      28688075015625 * Q * p < 56231561496331 * (Q+1) * D := by
    rcases hDcases with h45 | h69
    · have hpval : p = 89 := by omega
      rw [h45, hpval] at hcoef
      norm_num [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at hcoef
      have hhi : q4 ≤ 112 := by omega
      have hhi' : q4 ≤ 109 := by
        by_contra hn
        have hlo : 110 ≤ q4 := by omega
        interval_cases q4 <;> norm_num at hq4prime
      refine ⟨109, hhi', ?_⟩
      rw [h45, hpval]
      norm_num
    · have hpval : p = 137 := by omega
      rw [h69, hpval] at hcoef
      norm_num [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at hcoef
      have hhi : q4 ≤ 78 := by omega
      have hhi' : q4 ≤ 73 := by
        by_contra hn
        have hlo : 74 ≤ q4 := by omega
        interval_cases q4 <;> norm_num at hq4prime
      refine ⟨73, hhi', ?_⟩
      rw [h69, hpval]
      norm_num
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have hgeom := OddPerfectNumber.geom_mul_sub_one 23 (2*c+1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow23 : 23^4 ≤ 23^(2*c) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 23) (by omega)
  have h23 : 292561*23^(2*c) ≤ 279841*S23 := by dsimp [S23]; omega
  have hlast := OddPerfectNumber.geom_sum_last_two_terms_le q4 (2*e) (by omega)
  have hpowq : q4^(2*e) ≤ Q*q4^(2*e-1) := by
    calc
      q4^(2*e) = q4*q4^(2*e-1) := by
        conv_lhs => rw [show 2*e = (2*e-1)+1 by omega, pow_succ]
        ring
      _ ≤ Q*q4^(2*e-1) := Nat.mul_le_mul_right _ hqQ
  have hq : (Q+1)*q4^(2*e) ≤ Q*Sq := by
    calc
      (Q+1)*q4^(2*e) = Q*q4^(2*e)+q4^(2*e) := by ring
      _ ≤ Q*q4^(2*e)+Q*q4^(2*e-1) := Nat.add_le_add_left hpowq _
      _ = Q*(q4^(2*e)+q4^(2*e-1)) := by ring
      _ ≤ Q*Sq := Nat.mul_le_mul_left Q (by simpa [Sq] using hlast)
  have hl := Nat.mul_le_mul (Nat.mul_le_mul h3 h5) (Nat.mul_le_mul h23 hq)
  have hcross : (56231561496331*(Q+1))*m^2 ≤ (28688075015625*Q)*sigma := by
    calc
      (56231561496331*(Q+1))*m^2 =
          (9841*3^(2*a))*(19531*5^(2*b))*((292561*23^(2*c))*((Q+1)*q4^(2*e))) := by
        rw [hfac]; ring
      _ ≤ (6561*S3)*(15625*S5)*((279841*S23)*(Q*Sq)) := by
        simpa only [S3,S5,S23,Sq] using hl
      _ = (28688075015625*Q)*sigma := by rw [hsigma]; dsimp [S3,S5,S23,Sq]; ring
  have hineq : (56231561496331*(Q+1)*D)*m^2 ≤ (28688075015625*Q*p)*m^2 := by
    calc
      (56231561496331*(Q+1)*D)*m^2 = D*((56231561496331*(Q+1))*m^2) := by ring
      _ ≤ D*((28688075015625*Q)*sigma) := Nat.mul_le_mul_left D hcross
      _ = (28688075015625*Q)*(D*sigma) := by ring
      _ = (28688075015625*Q)*(p*m^2) := by rw [hrel]
      _ = (28688075015625*Q*p)*m^2 := by ring
  exact (not_lt_of_ge (Nat.le_of_mul_le_mul_right hineq hmpos)) hbad
