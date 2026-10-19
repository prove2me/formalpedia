-- Prove2me | solution 1 for SoficGroups.RankArcCharging.rankChangingArc_subset_crossing_or_unselected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/6c7792a6-c170-40ac-ba7c-7f04281dead6

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_RankArcCharging_selectedRankSupport_rank_eq

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.RankArcCharging
open scoped BigOperators
namespace SoficGroups.RankArcCharging
theorem _root_.solution
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (b : V → ℤ) (j : Finset V → ℤ)
    (w : Equiv.Perm V) :
    rankChangingArc U b w ⊆
      partitionWordCrossing P w ∪
        (U \ selectedRankSupport P b j) ∪
          rankSupportPreimageBad U (selectedRankSupport P b j) w := by
  intro x hx
  obtain ⟨hxU, hxchange⟩ := Finset.mem_filter.mp hx
  by_cases hxselected : x ∈ selectedRankSupport P b j
  · by_cases hcross : w x ∈ P.part x
    · by_cases hwselected : w x ∈ selectedRankSupport P b j
      · exfalso
        apply hxchange
        have hpart : P.part (w x) = P.part x :=
          P.part_eq_of_mem (P.part_mem.mpr hxU) hcross
        rw [selectedRankSupport_rank_eq P b j hwselected,
          selectedRankSupport_rank_eq P b j hxselected, hpart]
      · have hwU : w x ∈ U := P.part_subset x hcross
        exact Finset.mem_union_right _
          (Finset.mem_filter.mpr
            ⟨hxU, Finset.mem_sdiff.mpr ⟨hwU, hwselected⟩⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hxU, hcross⟩))
  · exact Finset.mem_union_left _
      (Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨hxU, hxselected⟩))
end SoficGroups.RankArcCharging
