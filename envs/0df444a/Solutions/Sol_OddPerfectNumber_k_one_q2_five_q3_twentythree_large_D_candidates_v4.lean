-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_candidates_v4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T23:27:33.762181+00:00
-- url     : https://prove2.me/submissions/eb7b3883-e8ac-47b2-b66f-c1b6f9eca0c8

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_q4_cases

theorem solution (D p q4 : Nat)
    (hDlow : 111 ≤ D) (hDhigh : D ≤ 685)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
    (hq4 : q4.Prime) (hq4gt : 47 < q4) (hq4le : q4 ≤ 61)
    (hq4dvd : q4 ∣ D) :
    (D = 159 ∧ p = 317 ∧ q4 = 53) ∨
    (D = 177 ∧ p = 353 ∧ q4 = 59) ∨
    (D = 427 ∧ p = 853 ∧ q4 = 61) ∨
    (D = 477 ∧ p = 953 ∧ q4 = 53) ∨
    (D = 531 ∧ p = 1061 ∧ q4 = 59) ∨
    (D = 549 ∧ p = 1097 ∧ q4 = 61) ∨
    (D = 649 ∧ p = 1297 ∧ q4 = 59) := by
  have hqcases := OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_q4_cases
    q4 hq4 hq4gt hq4le
  rcases hqcases with rfl | rfl | rfl
  · rcases hq4dvd with ⟨k, hk⟩
    have hklo : 3 ≤ k := by omega
    have hkbound : k ≤ 12 := by omega
    interval_cases k <;> norm_num [hk] at hp_eq
    all_goals subst p
    all_goals norm_num [hk] at hp4 <;> norm_num [hk] at hp <;> norm_num [hk]
  · rcases hq4dvd with ⟨k, hk⟩
    have hklo : 2 ≤ k := by omega
    have hkbound : k ≤ 11 := by omega
    interval_cases k <;> norm_num [hk] at hp_eq
    all_goals subst p
    all_goals norm_num [hk] at hp4 <;> norm_num [hk] at hp <;> norm_num [hk]
  · rcases hq4dvd with ⟨k, hk⟩
    have hklo : 2 ≤ k := by omega
    have hkbound : k ≤ 11 := by omega
    interval_cases k <;> norm_num [hk] at hp_eq
    all_goals subst p
    all_goals norm_num [hk] at hp4 <;> norm_num [hk] at hp <;> norm_num [hk]
