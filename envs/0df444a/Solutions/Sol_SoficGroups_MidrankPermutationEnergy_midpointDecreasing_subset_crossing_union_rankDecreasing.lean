-- Prove2me | solution 1 for SoficGroups.MidrankPermutationEnergy.midpointDecreasing_subset_crossing_union_rankDecreasing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/76e58e2c-b36a-471b-9514-92d53e4cda9c

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_componentVertexMidrank_mono

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.MidrankPermutationEnergy
namespace SoficGroups.MidrankPermutationEnergy
theorem _root_.solution
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (b : V → ℤ) (p : Equiv.Perm V) :
    midpointDecreasingVertices P b p ⊆
      partitionWordCrossing P p ∪ rankDecreasingVertices U b p := by
  intro x hx
  have hxmem := (Finset.mem_filter.mp hx).1
  have hxdec := (Finset.mem_filter.mp hx).2
  by_cases hcross : p x ∈ P.part x
  · apply Finset.mem_union.mpr
    right
    apply Finset.mem_filter.mpr
    refine ⟨hxmem, ?_⟩
    by_contra hnot
    have hrank : b x ≤ b (p x) := le_of_not_gt hnot
    have hpart : P.part x ∈ P.parts := P.part_mem.mpr hxmem
    have hsame : P.part (p x) = P.part x :=
      P.part_eq_of_mem hpart hcross
    have hmono := componentVertexMidrank_mono (P.part x) b hrank
    unfold partitionVertexMidrank at hxdec
    rw [hsame] at hxdec
    exact (not_lt_of_ge hmono) hxdec
  · apply Finset.mem_union.mpr
    left
    exact Finset.mem_filter.mpr ⟨hxmem, hcross⟩
end SoficGroups.MidrankPermutationEnergy
