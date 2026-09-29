-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_D_candidates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T18:25:58.032245+00:00
-- url     : https://prove2.me/submissions/d2e76a37-2c3c-411b-a74e-09ed0ef947e3

import Mathlib

theorem solution (D p q4 : Nat)
    (hDlow : 45 ≤ D) (hDhigh : D < 214)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
    (hq4 : q4.Prime) (hq4gt : 13 < q4) (hq4le : q4 ≤ 89)
    (hq4dvd : q4 ∣ D) :
    (D = 51 ∧ p = 101 ∧ q4 = 17) ∨
      (D = 57 ∧ p = 113 ∧ q4 = 19) ∨
      (D = 69 ∧ p = 137 ∧ q4 = 23) ∨
      (D = 79 ∧ p = 157 ∧ q4 = 79) ∨
      (D = 87 ∧ p = 173 ∧ q4 = 29) ∨
      (D = 115 ∧ p = 229 ∧ q4 = 23) ∨
      (D = 129 ∧ p = 257 ∧ q4 = 43) ∨
      (D = 141 ∧ p = 281 ∧ q4 = 47) ∨
      (D = 159 ∧ p = 317 ∧ q4 = 53) ∨
      (D = 177 ∧ p = 353 ∧ q4 = 59) ∨
      (D = 187 ∧ p = 373 ∧ q4 = 17) ∨
      (D = 201 ∧ p = 401 ∧ q4 = 67) ∨
      (D = 205 ∧ p = 409 ∧ q4 = 41) := by
  have hp_pos := hp.pos
  have hDpos : 0 < D := by
    rw [hp_eq] at hp_pos
    omega
  have hq4leD : q4 ≤ D := Nat.le_of_dvd hDpos hq4dvd
  subst p
  by_cases h90 : D < 90
  · have hupper : D ≤ 89 := by omega
    interval_cases D <;> norm_num at hp <;> norm_num
    all_goals interval_cases q4 <;> norm_num at *
  · by_cases h135 : D < 135
    · have hlower : 90 ≤ D := by omega
      have hupper : D ≤ 134 := by omega
      interval_cases D <;> norm_num at hp <;> norm_num
      all_goals interval_cases q4 <;> norm_num at *
    · by_cases h180 : D < 180
      · have hlower : 135 ≤ D := by omega
        have hupper : D ≤ 179 := by omega
        interval_cases D <;> norm_num at hp <;> norm_num
        all_goals interval_cases q4 <;> norm_num at *
      · have hlower : 180 ≤ D := by omega
        have hupper : D ≤ 213 := by omega
        interval_cases D <;> norm_num at hp <;> norm_num
        all_goals interval_cases q4 <;> norm_num at *
