-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_small_D_cases_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T08:07:10.978695+00:00
-- url     : https://prove2.me/submissions/54382a9a-c9f4-42d8-8164-c94e35f20e04

import Mathlib

theorem solution (D p q4 : Nat)
    (hDgt : 15 < D)
    (hDlt : D < 75)
    (hDodd : Odd D)
    (hp : p.Prime)
    (hp_eq : p = 2 * D - 1)
    (hq4gt : 29 < q4)
    (hDq : D < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4) :
    D = 27 ∨ D = 31 ∨ D = 37 ∨ D = 45 := by
  have hforbid : ∀ r, r.Prime → r ≠ 3 → r ≠ 5 → r ≠ 29 → r ∣ D → False := by
    intro r hr h3 h5 h29 hdiv
    rcases hDsupport r hr hdiv with hs | hs | hs | hs
    · exact h3 hs
    · exact h5 hs
    · exact h29 hs
    · subst r
      have hDpos : 0 < D := by
        exact Nat.pos_of_ne_zero (by
          intro hzero
          subst D
          norm_num at hDodd)
      have hq4leD : q4 ≤ D := Nat.le_of_dvd hDpos hdiv
      exact (Nat.not_lt_of_ge hq4leD) hDq
  have hnot7 : ¬ 7 ∣ D := by
    intro h; exact hforbid 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot11 : ¬ 11 ∣ D := by
    intro h; exact hforbid 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot13 : ¬ 13 ∣ D := by
    intro h; exact hforbid 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot17 : ¬ 17 ∣ D := by
    intro h; exact hforbid 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot19 : ¬ 19 ∣ D := by
    intro h; exact hforbid 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot23 : ¬ 23 ∣ D := by
    intro h; exact hforbid 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot31 : ¬ 31 ∣ D := by
    intro h; exact hforbid 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot37 : ¬ 37 ∣ D := by
    intro h; exact hforbid 37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot41 : ¬ 41 ∣ D := by
    intro h; exact hforbid 41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot43 : ¬ 43 ∣ D := by
    intro h; exact hforbid 43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot47 : ¬ 47 ∣ D := by
    intro h; exact hforbid 47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot53 : ¬ 53 ∣ D := by
    intro h; exact hforbid 53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot59 : ¬ 59 ∣ D := by
    intro h; exact hforbid 59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot61 : ¬ 61 ∣ D := by
    intro h; exact hforbid 61 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot67 : ¬ 67 ∣ D := by
    intro h; exact hforbid 67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot71 : ¬ 71 ∣ D := by
    intro h; exact hforbid 71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot73 : ¬ 73 ∣ D := by
    intro h; exact hforbid 73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hbound : D ≤ 74 := by omega
  interval_cases D
  all_goals (try norm_num at hDodd <;>
    try norm_num at hDgt <;>
    try norm_num [hp_eq] at hp <;>
    try norm_num at hnot7 <;>
    try norm_num at hnot11 <;>
    try norm_num at hnot13 <;>
    try norm_num at hnot17 <;>
    try norm_num at hnot19 <;>
    try norm_num at hnot23 <;>
    try norm_num at hnot31 <;>
    try norm_num at hnot37 <;>
    try norm_num at hnot41 <;>
    try norm_num at hnot43 <;>
    try norm_num at hnot47 <;>
    try norm_num at hnot53 <;>
    try norm_num at hnot59 <;>
    try norm_num at hnot61 <;>
    try norm_num at hnot67 <;>
    try norm_num at hnot71 <;>
    try norm_num at hnot73 <;>
    norm_num)
