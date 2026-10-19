-- Prove2me | solution 1 for SoficGroups.CompletedSourceChosenWordRestrictionTransfer.completedGenerator_permutationDistance_le_deleted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/a7dad757-f538-472e-88d9-520cf6d0cac8

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_card_subtypeBad
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_permutationDistance_le_subtypeBad
import Theorems.Thm_SoficGroups_MatchedComponentExitBudget_card_permutation_exit_le_deleted

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedSourceChosenWordRestrictionTransfer
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedComponentExitBudget
open SoficGroups.MatchedFirstStageWordRadiusTransfer
open scoped BigOperators
namespace SoficGroups.CompletedSourceChosenWordRestrictionTransfer
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (σ : Equiv.Perm V) (Z : Finset V)
    (τ : Equiv.Perm {x : V // x ∈ Z})
    (hagrees : ∀ x : {x : V // x ∈ Z},
      σ (x : V) ∈ Z →
        ((τ x : {x : V // x ∈ Z}) : V) = σ (x : V)) :
    SoficGroups.permutationDistance
      τ (completedRestriction σ Z) ≤
        (Finset.univ \ Z).card := by
  let E : Finset V := Z.filter fun x => σ x ∉ Z
  have hpoint : ∀ x : {x : V // x ∈ Z},
      (x : V) ∉ E → τ x = completedRestriction σ Z x := by
    intro x hx
    have hinside : σ (x : V) ∈ Z := by
      by_contra hout
      apply hx
      exact Finset.mem_filter.mpr ⟨x.property, hout⟩
    apply Subtype.ext
    calc
      ((τ x : {x : V // x ∈ Z}) : V) =
          σ (x : V) := hagrees x hinside
      _ = ((completedRestriction σ Z x :
          {x : V // x ∈ Z}) : V) := by
        symm
        exact completedRestriction_apply_of_mem
          σ Z x x.property hinside
  calc
    SoficGroups.permutationDistance
        τ (completedRestriction σ Z) ≤
      (subtypeBad Z E).card :=
        permutationDistance_le_subtypeBad Z E
          τ (completedRestriction σ Z) hpoint
    _ = (Z ∩ E).card := card_subtypeBad Z E
    _ ≤ E.card := Finset.card_le_card Finset.inter_subset_right
    _ ≤ (Finset.univ \ Z).card := by
      simpa only [E] using
        card_permutation_exit_le_deleted σ Z
end SoficGroups.CompletedSourceChosenWordRestrictionTransfer
