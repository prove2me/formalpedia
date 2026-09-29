-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_q4_cases
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T19:04:22.338394+00:00
-- url     : https://prove2.me/submissions/51fbc887-6d6e-4f58-90b1-20453f565d3b

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D57_q4_candidates
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D75_q4_candidate

theorem solution (D q4 : Nat) (hq4prime : q4.Prime)
    (hDq4range :
      (D = 57 ∧ 580 ≤ q4 ∧ q4 ≤ 602) ∨
      (D = 75 ∧ 261 ≤ q4 ∧ q4 ≤ 264)) :
    (D = 57 ∧ q4 = 587) ∨
      (D = 57 ∧ q4 = 593) ∨
      (D = 57 ∧ q4 = 599) ∨
      (D = 57 ∧ q4 = 601) ∨
      (D = 75 ∧ q4 = 263) := by
  rcases hDq4range with h57 | h75
  · rcases h57 with ⟨rfl, hlow, hhigh⟩
    have h := OddPerfectNumber.k_one_q2_five_q3_nineteen_D57_q4_candidates
      q4 hq4prime hlow hhigh
    rcases h with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · rcases h75 with ⟨rfl, hlow, hhigh⟩
    have h := OddPerfectNumber.k_one_q2_five_q3_nineteen_D75_q4_candidate
      q4 hq4prime hlow hhigh
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)))
