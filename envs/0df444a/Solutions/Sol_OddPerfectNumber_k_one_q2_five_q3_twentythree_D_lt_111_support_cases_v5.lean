-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T05:29:38.893975+00:00
-- url     : https://prove2.me/submissions/936498a6-5b43-46bc-9a3e-95f676d13020

import Mathlib

theorem solution (D p q4 : Nat)
    (hDlt : D < 111) (hDodd : Odd D) (hp : p.Prime)
    (hp_eq : p = 2 * D - 1) (hq4gt : 23 < q4) (hDq : D < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) :
    D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 27 ∨ D = 45 ∨ D = 69 ∨ D = 75 := by
  have hforbid : ∀ r, r.Prime → r ≠ 3 → r ≠ 5 → r ≠ 23 → r ∣ D → False := by
    intro r hr h3 h5 h23 hdiv
    rcases hDsupport r hr hdiv with hs | hs | hs | hs
    · exact h3 hs
    · exact h5 hs
    · exact h23 hs
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
  have hnot29 : ¬ 29 ∣ D := by
    intro h; exact hforbid 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
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
  have hnot79 : ¬ 79 ∣ D := by
    intro h; exact hforbid 79 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot83 : ¬ 83 ∣ D := by
    intro h; exact hforbid 83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot89 : ¬ 89 ∣ D := by
    intro h; exact hforbid 89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot97 : ¬ 97 ∣ D := by
    intro h; exact hforbid 97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot101 : ¬ 101 ∣ D := by
    intro h; exact hforbid 101 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot103 : ¬ 103 ∣ D := by
    intro h; exact hforbid 103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hnot107 : ¬ 107 ∣ D := by
    intro h; exact hforbid 107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  have hbound : D ≤ 110 := by omega
  by_cases hsmall : D ≤ 55
  · interval_cases D
    all_goals (try norm_num at hDodd <;> try norm_num [hp_eq] at hp <;> try norm_num at hnot7 <;> try norm_num at hnot11 <;> try norm_num at hnot13 <;> try norm_num at hnot17 <;> try norm_num at hnot19 <;> try norm_num at hnot29 <;> try norm_num at hnot31 <;> try norm_num at hnot37 <;> try norm_num at hnot41 <;> try norm_num at hnot43 <;> try norm_num at hnot47 <;> try norm_num at hnot53 <;> try norm_num at hnot59 <;> try norm_num at hnot61 <;> try norm_num at hnot67 <;> try norm_num at hnot71 <;> try norm_num at hnot73 <;> try norm_num at hnot79 <;> try norm_num at hnot83 <;> try norm_num at hnot89 <;> try norm_num at hnot97 <;> try norm_num at hnot101 <;> try norm_num at hnot103 <;> try norm_num at hnot107 <;> try norm_num)
  · have hlarge : 56 ≤ D := by omega
    interval_cases D
    all_goals (try norm_num at hDodd <;> try norm_num [hp_eq] at hp <;> try norm_num at hnot7 <;> try norm_num at hnot11 <;> try norm_num at hnot13 <;> try norm_num at hnot17 <;> try norm_num at hnot19 <;> try norm_num at hnot29 <;> try norm_num at hnot31 <;> try norm_num at hnot37 <;> try norm_num at hnot41 <;> try norm_num at hnot43 <;> try norm_num at hnot47 <;> try norm_num at hnot53 <;> try norm_num at hnot59 <;> try norm_num at hnot61 <;> try norm_num at hnot67 <;> try norm_num at hnot71 <;> try norm_num at hnot73 <;> try norm_num at hnot79 <;> try norm_num at hnot83 <;> try norm_num at hnot89 <;> try norm_num at hnot97 <;> try norm_num at hnot101 <;> try norm_num at hnot103 <;> try norm_num at hnot107 <;> try norm_num)
