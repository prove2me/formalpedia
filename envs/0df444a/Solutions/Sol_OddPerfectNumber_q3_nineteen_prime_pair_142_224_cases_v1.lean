-- Prove2me | solution 1 for OddPerfectNumber.q3_nineteen_prime_pair_142_224_cases_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T18:16:55.231195+00:00
-- url     : https://prove2.me/submissions/154af839-1982-466a-8616-b7b180d51234

import Mathlib

theorem solution (q4 p : Nat) (hq4prime : q4.Prime) (hp : p.Prime)
    (hp_eq : p = 2 * q4 - 1) (hq4ge : 142 ≤ q4) (hq4le : q4 ≤ 224) :
    q4 = 157 ∨ q4 = 199 ∨ q4 = 211 := by
  have hparts :
      q4 ≤ 163 ∨ (164 ≤ q4 ∧ q4 ≤ 185) ∨
        (186 ≤ q4 ∧ q4 ≤ 207) ∨ 208 ≤ q4 := by omega
  rcases hparts with hpart | hpart | hpart | hpart
  · interval_cases q4
    all_goals try norm_num [hp_eq] at hp
    all_goals try norm_num at hq4prime
    all_goals simp_all
  · interval_cases q4
    all_goals try norm_num [hp_eq] at hp
    all_goals try norm_num at hq4prime
    all_goals simp_all
  · interval_cases q4
    all_goals try norm_num [hp_eq] at hp
    all_goals try norm_num at hq4prime
    all_goals simp_all
  · interval_cases q4
    all_goals try norm_num [hp_eq] at hp
    all_goals try norm_num at hq4prime
    all_goals simp_all
