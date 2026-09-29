-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D45_abundance_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T00:39:59.137028+00:00
-- url     : https://prove2.me/submissions/ee71b91d-33c8-43e1-a15a-017b76e2dec7

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_ten
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hD : D = 45)
    (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4low : 46 ≤ q4) (hq4high : q4 ≤ 112)
    (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e) :
    False := by
  let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S23 := ∑ i ∈ Finset.range (2*c + 1), 23 ^ i
  let Sq := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_ten (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have hgeom := OddPerfectNumber.geom_mul_sub_one 23 (2*c + 1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow23 : 23 ^ 8 ≤ 23 ^ (2*c) := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < 23) (by omega)
  have h23 : 81870575521 * 23 ^ (2*c) ≤ 78310985281 * S23 := by
    dsimp [S23]
    omega
  have hlast := OddPerfectNumber.geom_sum_last_three_terms_le q4 (2*e) (by omega)
  have hpow1 : q4^(2*e) = q4^2 * q4^(2*e-2) := by
    calc
      q4^(2*e) = q4^((2*e-2)+2) := by congr 1 <;> omega
      _ = q4^2 * q4^(2*e-2) := by rw [pow_add]; ring
  have hpow2 : q4^(2*e-1) = q4 * q4^(2*e-2) := by
    calc
      q4^(2*e-1) = q4^((2*e-2)+1) := by congr 1 <;> omega
      _ = q4 * q4^(2*e-2) := by rw [pow_add]; ring
  have hqpoly : (q4^2 + q4 + 1) * q4^(2*e-2) ≤ Sq := by
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
  have hq2 : q4 * q4 ≤ 112 * q4 := by
    exact Nat.mul_le_mul_right q4 hq4high
  have hq2' : 113 * (q4 * q4) ≤ 113 * (112 * q4) :=
    Nat.mul_le_mul_left 113 hq2
  have hqcoef : 12657 * (q4 * q4) ≤
      12544 * (q4 * q4 + q4 + 1) := by
    calc
      12657 * (q4 * q4) = 12544 * (q4 * q4) + 113 * (q4 * q4) := by ring
      _ ≤ 12544 * (q4 * q4) + 113 * (112 * q4) := Nat.add_le_add_left hq2' _
      _ ≤ 12544 * (q4 * q4 + q4 + 1) := by omega
  have hq : 12657 * q4^(2*e) ≤ 12544 * Sq := by
    have hqpoly' : (q4*q4 + q4 + 1) * q4^(2*e-2) ≤ Sq := by
      simpa [pow_two] using hqpoly
    calc
      12657 * q4^(2*e) = 12657 * ((q4*q4) * q4^(2*e-2)) := by rw [hpow1]; ring
      _ ≤ 12544 * ((q4*q4 + q4 + 1) * q4^(2*e-2)) := by
        have ht := Nat.mul_le_mul_right (q4^(2*e-2)) hqcoef
        simpa [Nat.mul_assoc] using ht
      _ ≤ 12544 * Sq := Nat.mul_le_mul_left 12544 hqpoly'
  have hmul35 := Nat.mul_le_mul h3 h5
  have h23q := Nat.mul_le_mul h23 hq
  have hmul := Nat.mul_le_mul hmul35 h23q
  have hcross :
      1792604400083094856068111 *
          (3^(2*a) * 5^(2*b) * 23^(2*c) * q4^(2*e)) ≤
        906340332492122724000000 * (S3 * S5 * S23 * Sq) := by
    calc
      1792604400083094856068111 *
          (3^(2*a) * 5^(2*b) * 23^(2*c) * q4^(2*e)) =
          (88573*3^(2*a)) * (19531*5^(2*b)) *
            ((81870575521*23^(2*c)) * (12657*q4^(2*e))) := by ring
      _ ≤ (59049*S3) * (15625*S5) *
            ((78310985281*S23) * (12544*Sq)) := by
        simpa only [S3, S5, S23, Sq] using hmul
      _ = 906340332492122724000000 * (S3*S5*S23*Sq) := by ring
  have hmpos : 0 < m^2 := by rw [hfac]; positivity
  have hineq :
      1792604400083094856068111 * D * (m^2) ≤
        906340332492122724000000 * p * (m^2) := by
    have hmulD := Nat.mul_le_mul_left D hcross
    calc
      1792604400083094856068111 * D * (m^2) =
          D * (1792604400083094856068111 *
            (3^(2*a)*5^(2*b)*23^(2*c)*q4^(2*e))) := by rw [hfac]; ring
      _ ≤ D * (906340332492122724000000 * (S3*S5*S23*Sq)) := hmulD
      _ = 906340332492122724000000 * (D*sigma) := by rw [hsigma]; ring
      _ = 906340332492122724000000 * (p*(m^2)) := by rw [hrel]
      _ = 906340332492122724000000 * p * (m^2) := by ring
  have hconst :
      906340332492122724000000 * p <
        1792604400083094856068111 * D := by
    norm_num [hD, hp_eq]
  have hstrict :
      906340332492122724000000 * p * (m^2) <
        1792604400083094856068111 * D * (m^2) :=
    Nat.mul_lt_mul_of_pos_right hconst hmpos
  exact False.elim ((Nat.not_lt_of_ge hineq) hstrict)
