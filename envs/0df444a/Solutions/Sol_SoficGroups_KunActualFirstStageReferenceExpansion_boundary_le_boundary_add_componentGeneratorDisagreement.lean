-- Prove2me | solution 1 for SoficGroups.KunActualFirstStageReferenceExpansion.boundary_le_boundary_add_componentGeneratorDisagreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/e13be93a-9f8c-4587-a299-3f0b1064f47d

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFirstStageReferenceExpansion
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunActualFirstStageReferenceExpansion
theorem _root_.solution
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σref σact : ι → Equiv.Perm V)
    (C E : Finset V) (hEC : E ⊆ C) :
    SoficGroups.boundary σref E ≤
      SoficGroups.boundary σact E +
        componentGeneratorDisagreement C σref σact := by
  classical
  unfold SoficGroups.boundary componentGeneratorDisagreement
  calc
    (∑ i : ι, (E.filter fun x => σref i x ∉ E).card) ≤
        ∑ i : ι,
          ((E.filter fun x => σact i x ∉ E).card +
            (C.filter fun x => σref i x ≠ σact i x).card) := by
          apply Finset.sum_le_sum
          intro i _
          have hsubset :
              (E.filter fun x => σref i x ∉ E) ⊆
                (E.filter fun x => σact i x ∉ E) ∪
                  (C.filter fun x => σref i x ≠ σact i x) := by
            intro x hx
            obtain ⟨hxE, href⟩ := Finset.mem_filter.mp hx
            by_cases hact : σact i x ∈ E
            · apply Finset.mem_union_right
              apply Finset.mem_filter.mpr
              refine ⟨hEC hxE, ?_⟩
              intro heq
              apply href
              rwa [heq]
            · apply Finset.mem_union_left
              exact Finset.mem_filter.mpr ⟨hxE, hact⟩
          exact (Finset.card_le_card hsubset).trans
            (Finset.card_union_le _ _)
    _ = (∑ i : ι, (E.filter fun x => σact i x ∉ E).card) +
          ∑ i : ι,
            (C.filter fun x => σref i x ≠ σact i x).card := by
          rw [Finset.sum_add_distrib]
end SoficGroups.KunActualFirstStageReferenceExpansion
