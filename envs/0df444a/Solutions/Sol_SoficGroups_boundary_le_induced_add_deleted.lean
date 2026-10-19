-- Prove2me | solution 1 for SoficGroups.boundary_le_induced_add_deleted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/70edb372-5591-4ce9-a7fc-e3c4ab017219

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {V ι : Type*}
    [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B E : Finset V) :
    boundary σ E ≤ inducedBoundary σ B E + Fintype.card ι * B.card := by
  classical
  unfold boundary inducedBoundary
  calc
    (∑ i : ι, (E.filter fun x => σ i x ∉ E).card)
        ≤ ∑ i : ι,
          ((E.filter fun x => σ i x ∉ B ∧ σ i x ∉ E).card + B.card) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hpre : (E.filter fun x => σ i x ∈ B).card ≤ B.card := by
              rw [← Finset.card_map (σ i).toEmbedding]
              apply Finset.card_le_card
              intro y hy
              obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
              exact (Finset.mem_filter.mp hx).2
            have hsub :
                (E.filter fun x => σ i x ∉ E) ⊆
                  (E.filter fun x => σ i x ∉ B ∧ σ i x ∉ E) ∪
                    (E.filter fun x => σ i x ∈ B) := by
              intro x hx
              obtain ⟨hxE, hout⟩ := Finset.mem_filter.mp hx
              by_cases hB : σ i x ∈ B
              · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxE, hB⟩)
              · exact Finset.mem_union_left _
                  (Finset.mem_filter.mpr ⟨hxE, hB, hout⟩)
            exact (Finset.card_le_card hsub).trans
              ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hpre _))
    _ = (∑ i : ι, (E.filter fun x => σ i x ∉ B ∧ σ i x ∉ E).card) +
        Fintype.card ι * B.card := by simp [Finset.sum_add_distrib]
end SoficGroups
