-- Prove2me | solution 1 for WilliamsonShmoys.card_sum_of_partition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T19:32:13.42646+00:00
-- url     : https://prove2.me/submissions/e469a0fe-6b02-4c24-89b0-330f39d2a9a9

import Mathlib
theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (C : Finset (Finset V))
    (hcover : ∀ v : V, ∃ S, S ∈ C ∧ v ∈ S)
    (hdisjoint : ∀ S, S ∈ C → ∀ T, T ∈ C → S ≠ T → Disjoint S T) :
    (∑ S ∈ C, S.card) = Fintype.card V := by
  have hU : C.biUnion id = Finset.univ := by
    ext v
    simp only [Finset.mem_biUnion, id, Finset.mem_univ, iff_true]
    exact hcover v
  have hdis : (↑C : Set (Finset V)).PairwiseDisjoint id := by
    intro S hS T hT hne
    exact hdisjoint S hS T hT hne
  rw [← Finset.card_univ, ← hU, Finset.card_biUnion hdis]
  rfl
