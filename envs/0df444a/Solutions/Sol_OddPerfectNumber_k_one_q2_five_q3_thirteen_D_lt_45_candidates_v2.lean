-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_D_lt_45_candidates_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T18:18:17.847893+00:00
-- url     : https://prove2.me/submissions/a94c20a7-adeb-4c16-bf2c-2acac0b0b8ea

import Mathlib

theorem solution (D p q4 : Nat)
    (hD : D < 45) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hp_eq : p = 2 * D - 1)
    (hq4 : q4.Prime) (hq4gt : 13 < q4) (hq4dvd : q4 ∣ D) :
    (D = 19 ∧ p = 37 ∧ q4 = 19) ∨
      (D = 31 ∧ p = 61 ∧ q4 = 31) ∨
      (D = 37 ∧ p = 73 ∧ q4 = 37) := by
  have hp_pos := hp.pos
  have hDpos : 0 < D := by
    rw [hp_eq] at hp_pos
    omega
  have hq4le : q4 ≤ D := Nat.le_of_dvd hDpos hq4dvd
  subst p
  interval_cases D <;> norm_num at hp <;> norm_num
  all_goals interval_cases q4 <;> norm_num at *
