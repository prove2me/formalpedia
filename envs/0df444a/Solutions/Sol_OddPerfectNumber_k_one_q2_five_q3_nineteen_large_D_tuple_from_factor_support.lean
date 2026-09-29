-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_tuple_from_factor_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T15:55:51.75849+00:00
-- url     : https://prove2.me/submissions/ebf9d8ad-51e4-479c-aa6c-efc91e162d3c

import Mathlib

theorem solution (D p q4 i j k l : Nat)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4cases : q4 = 97 ∨ q4 = 101 ∨ q4 = 103 ∨ q4 = 107 ∨ q4 = 109 ∨ q4 = 113)
    (hform : D = 3^i * 5^j * 19^k * q4^l)
    (hi : i ≤ 7) (hj : j ≤ 5) (hk : k ≤ 2) (hl : l ≤ 1)
    (hwindow :
      (q4 = 97 ∧ 2881 ≤ D ∧ D ≤ 4608) ∨
      (q4 = 101 ∧ 854 ≤ D ∧ D ≤ 960) ∨
      (q4 = 103 ∧ 642 ≤ D ∧ D ≤ 699) ∨
      (q4 = 107 ∧ 437 ≤ D ∧ D ≤ 462) ∨
      (q4 = 109 ∧ 379 ≤ D ∧ D ≤ 398) ∨
      (q4 = 113 ∧ 304 ≤ D ∧ D ≤ 316)) :
    D = 855 ∧ q4 = 101 ∧ p = 1709 := by
  rcases hq4cases with h | h | h | h | h | h
  · subst q4
    have hwin : 2881 ≤ D ∧ D ≤ 4608 := by rcases hwindow with h' | h' | h' | h' | h' | h' <;> omega
    rcases hwin with ⟨hlo, hhi⟩
    interval_cases i <;> interval_cases j <;> interval_cases k <;> interval_cases l <;>
      norm_num at hform
    all_goals subst D
    all_goals (try norm_num at hlo)
    all_goals (try norm_num at hhi)
    all_goals have hp_local : p.Prime := hp
    all_goals norm_num [hp_eq] at hp_local
    all_goals norm_num [hp_eq]
  · subst q4
    have hwin : 854 ≤ D ∧ D ≤ 960 := by rcases hwindow with h' | h' | h' | h' | h' | h' <;> omega
    rcases hwin with ⟨hlo, hhi⟩
    interval_cases i <;> interval_cases j <;> interval_cases k <;> interval_cases l <;>
      norm_num at hform
    all_goals subst D
    all_goals (try norm_num at hlo)
    all_goals (try norm_num at hhi)
    all_goals have hp_local : p.Prime := hp
    all_goals norm_num [hp_eq] at hp_local
    all_goals norm_num [hp_eq]
  · subst q4
    have hwin : 642 ≤ D ∧ D ≤ 699 := by rcases hwindow with h' | h' | h' | h' | h' | h' <;> omega
    rcases hwin with ⟨hlo, hhi⟩
    interval_cases i <;> interval_cases j <;> interval_cases k <;> interval_cases l <;>
      norm_num at hform
    all_goals subst D
    all_goals (try norm_num at hlo)
    all_goals (try norm_num at hhi)
    all_goals have hp_local : p.Prime := hp
    all_goals norm_num [hp_eq] at hp_local
    all_goals norm_num [hp_eq]
  · subst q4
    have hwin : 437 ≤ D ∧ D ≤ 462 := by rcases hwindow with h' | h' | h' | h' | h' | h' <;> omega
    rcases hwin with ⟨hlo, hhi⟩
    interval_cases i <;> interval_cases j <;> interval_cases k <;> interval_cases l <;>
      norm_num at hform
    all_goals subst D
    all_goals (try norm_num at hlo)
    all_goals (try norm_num at hhi)
    all_goals have hp_local : p.Prime := hp
    all_goals norm_num [hp_eq] at hp_local
    all_goals norm_num [hp_eq]
  · subst q4
    have hwin : 379 ≤ D ∧ D ≤ 398 := by rcases hwindow with h' | h' | h' | h' | h' | h' <;> omega
    rcases hwin with ⟨hlo, hhi⟩
    interval_cases i <;> interval_cases j <;> interval_cases k <;> interval_cases l <;>
      norm_num at hform
    all_goals subst D
    all_goals (try norm_num at hlo)
    all_goals (try norm_num at hhi)
    all_goals have hp_local : p.Prime := hp
    all_goals norm_num [hp_eq] at hp_local
    all_goals norm_num [hp_eq]
  · subst q4
    have hwin : 304 ≤ D ∧ D ≤ 316 := by rcases hwindow with h' | h' | h' | h' | h' | h' <;> omega
    rcases hwin with ⟨hlo, hhi⟩
    interval_cases i <;> interval_cases j <;> interval_cases k <;> interval_cases l <;>
      norm_num at hform
    all_goals subst D
    all_goals (try norm_num at hlo)
    all_goals (try norm_num at hhi)
    all_goals have hp_local : p.Prime := hp
    all_goals norm_num [hp_eq] at hp_local
    all_goals norm_num [hp_eq]
