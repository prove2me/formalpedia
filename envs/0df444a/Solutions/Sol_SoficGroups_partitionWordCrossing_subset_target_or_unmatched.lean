-- Prove2me | solution 1 for SoficGroups.partitionWordCrossing_subset_target_or_unmatched
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/6aea0142-b31c-40cc-b855-f9a66775f58c

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_matched_partition_part_eq_of_target_part_eq

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P Q : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (D : Finset V → Finset V)
    (hD : ∀ C ∈ R, D C ∈ Q.parts)
    (hinj : Set.InjOn D (R : Set (Finset V)))
    (w : Equiv.Perm V) :
    partitionWordCrossing P w ⊆
      partitionWordCrossing Q w ∪
        (U \ matchedCore R D) ∪ matchedWordPreimageBad U R D w := by
  intro x hx
  obtain ⟨hxU, hxP⟩ := Finset.mem_filter.mp hx
  by_cases hxcore : x ∈ matchedCore R D
  · by_cases hxQ : w x ∈ Q.part x
    · have hwU : w x ∈ U := Q.part_subset x hxQ
      by_cases hwcore : w x ∈ matchedCore R D
      · have hQpart : Q.part x = Q.part (w x) :=
          (Q.part_eq_of_mem (Q.part_mem.mpr hxU) hxQ).symm
        have hPpart := matched_partition_part_eq_of_target_part_eq
          P Q R hR D hD hinj hxcore hwcore hQpart
        exfalso
        apply hxP
        rw [hPpart]
        exact P.mem_part hwU
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr
            ⟨hxU, Finset.mem_sdiff.mpr ⟨hwU, hwcore⟩⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxU, hxQ⟩))
  · exact Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxU, hxcore⟩))
end SoficGroups
