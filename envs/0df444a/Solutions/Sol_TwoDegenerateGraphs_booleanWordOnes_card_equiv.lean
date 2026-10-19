-- Prove2me | solution 1 for TwoDegenerateGraphs.booleanWordOnes_card_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/066034bc-4648-4950-9735-a1cfe6c8e7ff

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (equivalence : ι ≃ κ)
    (word : κ → Bool) :
    (booleanWordOnes (fun index : ι => word (equivalence index))).card =
      (booleanWordOnes word).card := by
  classical
  apply Finset.card_bij
    (fun index _ => equivalence index)
  · intro index hindex
    have hone := (Finset.mem_filter.mp hindex).2
    unfold booleanWordOnes
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hone⟩
  · intro first _ second _ hequal
    exact equivalence.injective hequal
  · intro index hindex
    refine ⟨equivalence.symm index, ?_, equivalence.apply_symm_apply index⟩
    unfold booleanWordOnes
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hone := (Finset.mem_filter.mp hindex).2
    simpa using hone
end TwoDegenerateGraphs
