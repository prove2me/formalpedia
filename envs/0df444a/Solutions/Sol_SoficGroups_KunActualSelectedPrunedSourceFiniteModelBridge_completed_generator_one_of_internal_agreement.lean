-- Prove2me | solution 1 for SoficGroups.KunActualSelectedPrunedSourceFiniteModelBridge.completed_generator_one_of_internal_agreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/30b0d517-a5aa-4f88-9360-efc3618e58c9

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSelectedPrunedSourceFiniteModelBridge
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.KunActualSoficRootRadius
open scoped BigOperators Pointwise
namespace SoficGroups.KunActualSelectedPrunedSourceFiniteModelBridge
theorem _root_.solution
    {G : Type} [Group G] (S : Finset G)
    {W : Type}
    (σ : ↥S → Equiv.Perm W) (Z : Finset W)
    (τ : ↥S → Equiv.Perm {x : W // x ∈ Z})
    (hagrees : ∀ i (x : W) (hx : x ∈ Z)
      (_hi : σ i x ∈ Z),
        ((τ i ⟨x, hx⟩ : {x : W // x ∈ Z}) : W) = σ i x)
    (hidentity : ∀ i : ↥S, (i : G) = 1 → σ i = 1)
    (i : ↥S) (hi : (i : G) = 1) : τ i = 1 := by
  have hσ : σ i = 1 := hidentity i hi
  ext x
  have hinside : σ i (x : W) ∈ Z := by
    rw [hσ]
    exact x.property
  simpa [hσ] using hagrees i (x : W) x.property hinside
end SoficGroups.KunActualSelectedPrunedSourceFiniteModelBridge
