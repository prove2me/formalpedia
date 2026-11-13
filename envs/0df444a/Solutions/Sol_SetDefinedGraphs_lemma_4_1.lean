-- Prove2me | solution 1 for SetDefinedGraphs.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:21:50.164792+00:00
-- url     : https://prove2.me/submissions/e522c089-567e-4649-9689-e51dfcd720c1

import Mathlib
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets
import Definitions.Def_SetDefinedGraphs_Clauses

section
set_option autoImplicit false
namespace SetDefinedGraphs
theorem chk_lemma_4_1 {d : ℕ} (P : Setoid (Fin d)) (C : FullClause (Fin d)) (hC : ¬ IsPCompatible P C)
    (u w : Fin d → ℕ) (hu : IsPHomogeneousVec P u) (hw : IsPHomogeneousVec P w) :
    eqPattern u w ≠ C := by
  intro h
  apply hC
  have hCij : ∀ i j, C i j = true ↔ u i = w j := by
    intro i j
    rw [← h]; simp [eqPattern]
  constructor
  · intro i
    by_cases hex : ∃ j0, C i j0 = true
    · right
      obtain ⟨j0, hj0⟩ := hex
      refine ⟨j0, fun j => ?_⟩
      rw [hCij] at hj0
      rw [hCij, hj0, hw]
      exact ⟨fun h => P.symm h, fun h => P.symm h⟩
    · left
      intro j
      by_contra hne
      exact hex ⟨j, by simpa using hne⟩
  · intro j
    by_cases hex : ∃ i0, C i0 j = true
    · right
      obtain ⟨i0, hi0⟩ := hex
      refine ⟨i0, fun i => ?_⟩
      rw [hCij] at hi0
      rw [hCij, ← hi0, ← hu]
    · left
      intro i
      by_contra hne
      exact hex ⟨i, by simpa using hne⟩
end SetDefinedGraphs
end

theorem solution : type_of% @SetDefinedGraphs.chk_lemma_4_1 := @SetDefinedGraphs.chk_lemma_4_1
