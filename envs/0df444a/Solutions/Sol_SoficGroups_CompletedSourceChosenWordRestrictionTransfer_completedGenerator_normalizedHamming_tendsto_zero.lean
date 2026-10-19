-- Prove2me | solution 1 for SoficGroups.CompletedSourceChosenWordRestrictionTransfer.completedGenerator_normalizedHamming_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/e159a8ad-e6a7-4854-97be-b7d8374c1a6b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_normalizedHamming_nonneg
import Theorems.Thm_SoficGroups_CompletedSourceChosenWordRestrictionTransfer_completedGenerator_normalizedHamming_le_deleted

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
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (σ : (n : ℕ) → Equiv.Perm (V n))
    (Z : (n : ℕ) → Finset (V n))
    (τ : (n : ℕ) → Equiv.Perm {x : V n // x ∈ Z n})
    (hagrees : ∀ n, ∀ x : {x : V n // x ∈ Z n},
      σ n (x : V n) ∈ Z n →
        ((τ n x : {x : V n // x ∈ Z n}) : V n) =
          σ n (x : V n))
    (hdeleted : Tendsto
      (fun n => (((Finset.univ \ Z n).card : ℝ) / (Z n).card))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        SoficGroups.normalizedHamming
          (τ n) (completedRestriction (σ n) (Z n)))
      atTop (nhds 0) := by
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      SoficGroups.normalizedHamming_nonneg
        (τ n) (completedRestriction (σ n) (Z n)))
    (Filter.Eventually.of_forall fun n =>
      completedGenerator_normalizedHamming_le_deleted
        (σ n) (Z n) (τ n) (hagrees n))
    hdeleted
end SoficGroups.CompletedSourceChosenWordRestrictionTransfer
