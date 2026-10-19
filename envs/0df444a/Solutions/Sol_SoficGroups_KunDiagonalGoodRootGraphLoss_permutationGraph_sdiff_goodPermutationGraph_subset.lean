-- Prove2me | solution 1 for SoficGroups.KunDiagonalGoodRootGraphLoss.permutationGraph_sdiff_goodPermutationGraph_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/5f568e72-d926-4290-9467-e4ae2ebe146b

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDiagonalGoodRootGraphLoss
open scoped BigOperators symmDiff
namespace SoficGroups.KunDiagonalGoodRootGraphLoss
theorem _root_.solution {V : Type*}
    [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (B : Finset V) :
    SoficGroups.permutationGraph p \ goodPermutationGraph p B ⊆
      ((SoficGroups.permutationGraph p).filter fun z => z.1 ∈ B) ∪
        ((SoficGroups.permutationGraph p).filter fun z => z.2 ∈ B) := by
  intro z hz
  obtain ⟨hzgraph, hzgood⟩ := Finset.mem_sdiff.mp hz
  by_cases hfirst : z.1 ∈ B
  · exact Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hzgraph, hfirst⟩)
  · have hsecond : z.2 ∈ B := by
      by_contra h
      apply hzgood
      exact Finset.mem_filter.mpr ⟨hzgraph, hfirst, h⟩
    exact Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨hzgraph, hsecond⟩)
end SoficGroups.KunDiagonalGoodRootGraphLoss
