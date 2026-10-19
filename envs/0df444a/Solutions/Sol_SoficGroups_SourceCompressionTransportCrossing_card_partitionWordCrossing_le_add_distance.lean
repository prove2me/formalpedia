-- Prove2me | solution 1 for SoficGroups.SourceCompressionTransportCrossing.card_partitionWordCrossing_le_add_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/79038fd5-37e1-4f41-8bb9-bff9fcc9736e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceCompressionTransportCrossing_mem_partitionWordCrossing_univ

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionTransportCrossing
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceCompressionTransportCrossing
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (p q : Equiv.Perm V) :
    (SoficGroups.partitionWordCrossing Q p).card ≤
      (SoficGroups.partitionWordCrossing Q q).card +
        SoficGroups.permutationDistance p q := by
  classical
  have hsub :
      SoficGroups.partitionWordCrossing Q p ⊆
        SoficGroups.partitionWordCrossing Q q ∪
          Finset.univ.filter (fun x : V => p x ≠ q x) := by
    intro x hx
    by_cases heq : p x = q x
    · apply Finset.mem_union_left
      apply (mem_partitionWordCrossing_univ Q q x).2
      have hp := (mem_partitionWordCrossing_univ Q p x).1 hx
      simpa [heq] using hp
    · apply Finset.mem_union_right
      exact Finset.mem_filter.2 ⟨Finset.mem_univ x, heq⟩
  calc
    (SoficGroups.partitionWordCrossing Q p).card ≤
        (SoficGroups.partitionWordCrossing Q q ∪
          Finset.univ.filter (fun x : V => p x ≠ q x)).card :=
      Finset.card_le_card hsub
    _ ≤ (SoficGroups.partitionWordCrossing Q q).card +
        (Finset.univ.filter (fun x : V => p x ≠ q x)).card :=
      Finset.card_union_le _ _
    _ = (SoficGroups.partitionWordCrossing Q q).card +
        SoficGroups.permutationDistance p q := by
      simp [SoficGroups.permutationDistance, hammingDist]
end SoficGroups.SourceCompressionTransportCrossing
