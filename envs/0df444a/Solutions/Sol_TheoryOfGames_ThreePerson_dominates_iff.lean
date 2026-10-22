-- Prove2me | solution 1 for TheoryOfGames.ThreePerson.dominates_iff
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:58:25.202473+00:00
-- url     : https://prove2.me/submissions/09326f72-1ea1-44de-9a0a-7e71ff17035d

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution
import Definitions.Def_TheoryOfGames_ThreePerson_ReducedThreePerson

set_option autoImplicit false
open TheoryOfGames.ThreePerson

theorem solution (α β : Fin 3 → ℝ) (hα : IsImputation redV α)
    (hβ : IsImputation redV β) :
    Dominates redV α β ↔
      (β 0 < α 0 ∧ β 1 < α 1) ∨ (β 0 < α 0 ∧ β 2 < α 2) ∨ (β 1 < α 1 ∧ β 2 < α 2) := by
  obtain ⟨hα1, hα2⟩ := hα
  obtain ⟨hβ1, hβ2⟩ := hβ
  have hv1 : ∀ i : Fin 3, redV {i} = -1 := fun i => by simp [redV]
  have hα1' : ∀ i, -1 ≤ α i := fun i => by simpa [hv1 i] using hα1 i
  have hβ1' : ∀ i, -1 ≤ β i := fun i => by simpa [hv1 i] using hβ1 i
  rw [Fin.sum_univ_three] at hα2 hβ2
  constructor
  · rintro ⟨S, hS, heff, hlt⟩
    by_cases hc : S.card = 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
      have h1 := heff
      simp only [IsEffective, Finset.sum_singleton, hv1] at h1
      have h2 := hlt i (Finset.mem_singleton_self i)
      have := hβ1' i
      linarith
    · have h2 : 1 < S.card := by
        have := hS.card_pos
        omega
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h2
      have hi' := hlt i hi
      have hj' := hlt j hj
      fin_cases i <;> fin_cases j <;> simp at hij <;> simp at hi' hj' <;> tauto
  · intro h
    have e2 : ∀ i j : Fin 3, i ≠ j → redV {i, j} = 1 := by
      intro i j hij
      simp [redV, Finset.card_pair hij]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨{0, 1}, by simp, ?_, ?_⟩
      · simp only [IsEffective]
        rw [e2 0 1 (by decide)]
        simp [Finset.sum_pair (show (0 : Fin 3) ≠ 1 by decide)]
        linarith [hα1' 2]
      · intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption
    · refine ⟨{0, 2}, by simp, ?_, ?_⟩
      · simp only [IsEffective]
        rw [e2 0 2 (by decide)]
        simp [Finset.sum_pair (show (0 : Fin 3) ≠ 2 by decide)]
        linarith [hα1' 1]
      · intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption
    · refine ⟨{1, 2}, by simp, ?_, ?_⟩
      · simp only [IsEffective]
        rw [e2 1 2 (by decide)]
        simp [Finset.sum_pair (show (1 : Fin 3) ≠ 2 by decide)]
        linarith [hα1' 0]
      · intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption
