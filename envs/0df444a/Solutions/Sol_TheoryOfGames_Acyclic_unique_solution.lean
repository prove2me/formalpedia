-- Prove2me | solution 1 for TheoryOfGames.Acyclic.unique_solution
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-03T15:27:30.851887+00:00
-- url     : https://prove2.me/submissions/4dc87f22-ff84-4ade-a89d-510b81134a43

import Theorems.Thm_TheoryOfGames_Acyclic_eq_V0_of_isSolution
import Theorems.Thm_TheoryOfGames_Acyclic_V0_isSolution

open TheoryOfGames.Acyclic

theorem solution {α : Type*} (D : Set α) (S : α → α → Prop)
    (hD : D.Finite) (hS : IsAcyclic D S) :
    (∃! V : Set α, IsSolution D S V) ∧
      ∀ V : Set α, IsSolution D S V ↔ V = V0 D S := by
  have h0 := V0_isSolution D S hD hS
  have heq := eq_V0_of_isSolution D S hD hS
  refine ⟨⟨V0 D S, h0, heq⟩, ?_⟩
  intro V
  exact ⟨heq V, fun h => h.symm ▸ h0⟩
