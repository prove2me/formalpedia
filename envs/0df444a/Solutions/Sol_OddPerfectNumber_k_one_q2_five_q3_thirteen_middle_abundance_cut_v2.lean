-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_abundance_cut_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T01:51:20.333046+00:00
-- url     : https://prove2.me/submissions/6d4761f2-e880-4525-b4a7-c5cc00be6617

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_two_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirteen_ge_two
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_base_le47

theorem solution
    (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hcases :
      (D = 51 ∧ p = 101 ∧ q4 = 17) ∨
      (D = 57 ∧ p = 113 ∧ q4 = 19) ∨
      (D = 69 ∧ p = 137 ∧ q4 = 23) ∨
      (D = 87 ∧ p = 173 ∧ q4 = 29) ∨
      (D = 115 ∧ p = 229 ∧ q4 = 23) ∨
      (D = 129 ∧ p = 257 ∧ q4 = 43) ∨
      (D = 141 ∧ p = 281 ∧ q4 = 47) ∨
      (D = 187 ∧ p = 373 ∧ q4 = 17) ∨
      (D = 205 ∧ p = 409 ∧ q4 = 41))
    (hq4prime : q4.Prime) (hq4le : q4 ≤ 47)
    (ha : 2 ≤ a) (hb : 8 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    False := by
  let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S13 := ∑ i ∈ Finset.range (2*c + 1), 13 ^ i
  let Sq4 := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have ha' : 2 ≤ 2*a := by omega
  have hb' : 6 ≤ 2*b := by omega
  have hc' : 2 ≤ 2*c := by omega
  have he' : 2 ≤ 2*e := by omega
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_two_sharp (2*a) ha'
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six (2*b) hb'
  have h13 := OddPerfectNumber.geom_ratio_lower_thirteen_ge_two (2*c) hc'
  have hq4 := OddPerfectNumber.geom_ratio_lower_base_le47 q4 (2*e) hq4le he'
  have hmul35 := Nat.mul_le_mul h3 h5
  have hmul13q4 := Nat.mul_le_mul h13 hq4
  have hmul := Nat.mul_le_mul hmul35 hmul13q4
  have hcross :
      446033952 * (3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e)) ≤
        223396875 * (S3 * S5 * S13 * Sq4) := by
    calc
      446033952 * (3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e)) =
          (13 * 3 ^ (2*a)) * (3906 * 5 ^ (2*b)) *
            ((183 * 13 ^ (2*c)) * (48 * q4 ^ (2*e))) := by ring
      _ ≤ (9 * S3) * (3125 * S5) * ((169 * S13) * (47 * Sq4)) := by
        simpa only [S3, S5, S13, Sq4] using hmul
      _ = 223396875 * (S3 * S5 * S13 * Sq4) := by ring
  have hq4pos : 0 < q4 := hq4prime.pos
  have hmpos : 0 < m ^ 2 := by
    rw [hfac]
    exact mul_pos (mul_pos (mul_pos (pow_pos (by norm_num) (2*a))
      (pow_pos (by norm_num) (2*b))) (pow_pos (by norm_num) (2*c)))
      (pow_pos hq4pos (2*e))
  have hineq : 446033952 * D * (m ^ 2) ≤ 223396875 * p * (m ^ 2) := by
    have hmulD := Nat.mul_le_mul_left D hcross
    have hraw :
        446033952 * D * (3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e)) ≤
          223396875 * D * (S3 * S5 * S13 * Sq4) := by
      calc
        446033952 * D * (3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e)) =
            D * (446033952 * (3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))) := by ring
        _ ≤ D * (223396875 * (S3 * S5 * S13 * Sq4)) := hmulD
        _ = 223396875 * D * (S3 * S5 * S13 * Sq4) := by ring
    calc
      446033952 * D * (m ^ 2) =
          446033952 * D * (3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e)) := by rw [hfac]
      _ ≤ 223396875 * D * (S3 * S5 * S13 * Sq4) := hraw
      _ = 223396875 * D * sigma := by rw [hsigma]
      _ = 223396875 * (D * sigma) := by ring
      _ = 223396875 * (p * (m ^ 2)) := by rw [hrel]
      _ = 223396875 * p * (m ^ 2) := by ring
  rcases hcases with h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨hD, hp, hq⟩
  all_goals
    have hconst : 223396875 * p < 446033952 * D := by norm_num [hD, hp]
    have hstrict : 223396875 * p * (m ^ 2) < 446033952 * D * (m ^ 2) := by
      exact Nat.mul_lt_mul_of_pos_right hconst hmpos
    exact False.elim ((Nat.not_lt_of_ge hineq) hstrict)
