-- Prove2me | solution 1 for SoficGroups.CompletedSourceChosenWordRestrictionTransfer.completedGenerator_normalizedHamming_le_deleted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/9d558e4a-6327-4a81-a630-2f00a6c984da

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_CompletedSourceChosenWordRestrictionTransfer_completedGenerator_permutationDistance_le_deleted

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
    SoficGroups.normalizedHamming
      τ (completedRestriction σ Z) ≤
        (((Finset.univ \ Z).card : ℝ) / Z.card) := by
  have hnat :=
    completedGenerator_permutationDistance_le_deleted
      σ Z τ hagrees
  have hreal :
      (SoficGroups.permutationDistance
        τ (completedRestriction σ Z) : ℝ) ≤
          (Finset.univ \ Z).card := by
    exact_mod_cast hnat
  have hdiv := div_le_div_of_nonneg_right hreal
    (show (0 : ℝ) ≤ (Z.card : ℝ) by positivity)
  simpa only [SoficGroups.normalizedHamming,
    SoficGroups.permutationDistance, Fintype.card_coe] using hdiv
end SoficGroups.CompletedSourceChosenWordRestrictionTransfer
