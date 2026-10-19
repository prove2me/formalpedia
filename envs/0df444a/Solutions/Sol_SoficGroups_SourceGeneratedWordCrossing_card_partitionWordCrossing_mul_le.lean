-- Prove2me | solution 1 for SoficGroups.SourceGeneratedWordCrossing.card_partitionWordCrossing_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/df11073b-edf6-4aa4-88a4-6b8d0ecd90c9

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceCompressionTransportCrossing_mem_partitionWordCrossing_univ
import Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_mem_partitionWordCrossing_univ

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceGeneratedWordCrossing
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceGeneratedWordCrossing
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (p q : Equiv.Perm V) :
    (SoficGroups.partitionWordCrossing Q (p * q)).card ≤
      (SoficGroups.partitionWordCrossing Q p).card +
        (SoficGroups.partitionWordCrossing Q q).card := by
  classical
  have hsub :
      SoficGroups.partitionWordCrossing Q (p * q) ⊆
        SoficGroups.partitionWordCrossing Q q ∪
          (SoficGroups.partitionWordCrossing Q p).map
            q.symm.toEmbedding := by
    intro x hx
    have hpq := (mem_partitionWordCrossing_univ Q (p * q) x).1 hx
    by_cases hq : Q.part x ≠ Q.part (q x)
    · exact Finset.mem_union_left _
        ((mem_partitionWordCrossing_univ Q q x).2 hq)
    · apply Finset.mem_union_right
      apply Finset.mem_map.2
      refine ⟨q x, (mem_partitionWordCrossing_univ Q p (q x)).2 ?_,
        by simp⟩
      intro heq
      apply hpq
      have hpart : Q.part x = Q.part (q x) := not_ne_iff.mp hq
      simpa [Equiv.Perm.mul_apply] using hpart.trans heq
  have hcard := (Finset.card_le_card hsub).trans
    (Finset.card_union_le
      (SoficGroups.partitionWordCrossing Q q)
      ((SoficGroups.partitionWordCrossing Q p).map
        q.symm.toEmbedding))
  simpa [Nat.add_comm] using hcard
end SoficGroups.SourceGeneratedWordCrossing
