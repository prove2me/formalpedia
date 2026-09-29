-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D87_q4_29_abundance_absurd_v5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T06:28:59.911624+00:00
-- url     : https://prove2.me/submissions/64c8d364-47c2-4f99-b97a-3777a2efc397

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_ten
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hD : D = 87)
    (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4eq : q4 = 29)
    (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) : False := by
  let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S29 := ∑ i ∈ Finset.range (2*c + 1), 29 ^ i
  let Sq := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_ten (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have h29last := OddPerfectNumber.geom_sum_last_two_terms_le 29 (2*c) (by omega)
  have hq4last := OddPerfectNumber.geom_sum_last_two_terms_le q4 (2*e) (by omega)
  have h29 : 30 * 29^(2*c) ≤ 29 * S29 := by
    dsimp [S29] at h29last ⊢
    have hp : 29^(2*c) = 29 * 29^(2*c-1) := by
      calc
        29^(2*c) = 29^((2*c-1)+1) := by congr 1 <;> omega
        _ = 29^(2*c-1) * 29 := by rw [pow_succ]
        _ = 29 * 29^(2*c-1) := by ring
    calc
      30 * 29^(2*c) = 29 * 29^(2*c) + 29^(2*c) := by ring
      _ = 29 * 29^(2*c) + 29 * 29^(2*c-1) := by rw [hp]
      _ ≤ 29 * (29^(2*c) + 29^(2*c-1)) := by omega
      _ ≤ 29 * (∑ i ∈ Finset.range (2*c+1), 29^i) := by omega
  have hq : 30 * q4^(2*e) ≤ 29 * Sq := by
    dsimp [Sq] at hq4last ⊢
    rw [hq4eq] at hq4last ⊢
    have hp : 29^(2*e) = 29 * 29^(2*e-1) := by
      calc
        29^(2*e) = 29^((2*e-1)+1) := by congr 1 <;> omega
        _ = 29^(2*e-1) * 29 := by rw [pow_succ]
        _ = 29 * 29^(2*e-1) := by ring
    calc
      30 * 29^(2*e) = 29 * 29^(2*e) + 29^(2*e) := by ring
      _ = 29 * 29^(2*e) + 29 * 29^(2*e-1) := by rw [hp]
      _ ≤ 29 * (29^(2*e) + 29^(2*e-1)) := by omega
      _ ≤ 29 * (∑ i ∈ Finset.range (2*e+1), 29^i) := by omega
  have hmul35 := Nat.mul_le_mul h3 h5
  have hmul29 := Nat.mul_le_mul h29 hq
  have hmul := Nat.mul_le_mul hmul35 hmul29
  have hcross :
      1556927336700 * (3^(2*a) * 5^(2*b) * 29^(2*c) * q4^(2*e)) ≤
        775940765625 * (S3 * S5 * S29 * Sq) := by
    calc
      1556927336700 * (3^(2*a) * 5^(2*b) * 29^(2*c) * q4^(2*e)) =
          (88573*3^(2*a)) * (19531*5^(2*b)) *
            ((30*29^(2*c)) * (30*q4^(2*e))) := by ring
      _ ≤ (59049*S3) * (15625*S5) *
            ((29*S29) * (29*Sq)) := by
        simpa only [S3, S5, S29, Sq] using hmul
      _ = 775940765625 * (S3*S5*S29*Sq) := by ring
  have hmpos : 0 < m^2 := by rw [hfac]; positivity
  have hineq :
      1556927336700 * D * (m^2) ≤
        775940765625 * p * (m^2) := by
    have hmulD := Nat.mul_le_mul_left D hcross
    calc
      1556927336700 * D * (m^2) =
          D * (1556927336700 *
            (3^(2*a)*5^(2*b)*29^(2*c)*q4^(2*e))) := by rw [hfac]; ring
      _ ≤ D * (775940765625 * (S3*S5*S29*Sq)) := hmulD
      _ = 775940765625 * (D*sigma) := by rw [hsigma]; ring
      _ = 775940765625 * (p*(m^2)) := by rw [hrel]
      _ = 775940765625 * p * (m^2) := by ring
  have hconst : 775940765625 * p < 1556927336700 * D := by
    norm_num [hD, hp_eq]
  have hstrict : 775940765625 * p * (m^2) < 1556927336700 * D * (m^2) :=
    Nat.mul_lt_mul_of_pos_right hconst hmpos
  exact False.elim ((Nat.not_lt_of_ge hineq) hstrict)
