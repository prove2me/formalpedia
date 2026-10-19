-- Prove2me | solution 1 for SoficGroups.boundary_union_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/9b9dec89-4e31-4ef9-810a-74e6846f19f6

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B E : Finset V) :
    boundary σ (B ∪ E) ≤ boundary σ B + inducedBoundary σ B E := by
  classical
  unfold boundary inducedBoundary
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  apply le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_union] at hx ⊢
  rcases hx with ⟨hxB | hxE, hout⟩
  · exact Or.inl ⟨hxB, fun h => hout (Or.inl h)⟩
  · exact Or.inr
      ⟨hxE, fun h => hout (Or.inl h), fun h => hout (Or.inr h)⟩
end SoficGroups
