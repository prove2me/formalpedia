-- Prove2me | solution 1 for RevenueManagement.second_price_dominant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T21:25:04.208346+00:00
-- url     : https://prove2.me/submissions/f69bd137-7038-4dfc-8b82-f53fe4617d9c

import Mathlib
import Definitions.Def_RevenueManagement_auctions

set_option autoImplicit false

open RevenueManagement in
theorem solution {m : ℕ} (v b : ℝ) (others : Fin m → ℝ) :
    spSurplus v b others ≤ spSurplus v v others := by
  unfold spSurplus
  have hbdd : BddAbove (Set.range others) := (Set.finite_range others).bddAbove
  by_cases hA : ∀ j, others j < b
  · by_cases hB : ∀ j, others j < v
    · rw [if_pos hA, if_pos hB]
    · rw [if_pos hA, if_neg hB]
      simp only [not_forall, not_lt] at hB
      obtain ⟨j, hj⟩ := hB
      have := le_csSup hbdd (Set.mem_range_self j)
      linarith
  · by_cases hB : ∀ j, others j < v
    · rw [if_neg hA, if_pos hB]
      simp only [not_forall, not_lt] at hA
      obtain ⟨j, _⟩ := hA
      have hne : (Set.range others).Nonempty := ⟨others j, Set.mem_range_self j⟩
      have : sSup (Set.range others) ≤ v := by
        apply csSup_le hne
        rintro _ ⟨i, rfl⟩
        exact (hB i).le
      linarith
    · rw [if_neg hA, if_neg hB]
