-- Prove2me | solution 1 for SoficGroups.KunActualTwicePrunedFirstFactorRootBad.completedRestriction_mul_distance_le_failure_add_deleted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/c2caaf29-58ca-4ee7-911e-b3336d051f5c

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_card_subtypeBad
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_permutationDistance_le_subtypeBad
import Theorems.Thm_SoficGroups_MatchedComponentExitBudget_card_permutation_exit_le_deleted
import Theorems.Thm_SoficGroups_KunActualTwicePrunedFirstFactorRootBad_completedRestriction_mul_of_not_mem_restrictionMultiplicationBad

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualTwicePrunedFirstFactorRootBad
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedComponentExitBudget
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open SoficGroups.CompletedSourceFinalGeneratorTransfer
open scoped BigOperators Pointwise
namespace SoficGroups.KunActualTwicePrunedFirstFactorRootBad
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (p q r : Equiv.Perm V) (Z : Finset V) :
    SoficGroups.permutationDistance
        (completedRestriction r Z)
        (completedRestriction p Z * completedRestriction q Z) ≤
      (Finset.univ.filter fun x : V => r x ≠ p (q x)).card +
        2 * (Finset.univ \ Z).card := by
  classical
  let B : Finset V := restrictionMultiplicationBad p q r Z
  let E₁ : Finset V := Z.filter fun x => q x ∉ Z
  let E₂ : Finset V := Z.filter fun x => r x ∉ Z
  let E₃ : Finset V := Finset.univ.filter fun x : V => r x ≠ p (q x)
  have hsubset : B ⊆ E₁ ∪ E₂ ∪ E₃ := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    rcases hx'.2 with hq | hr | hmul
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx'.1, hq⟩))
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx'.1, hr⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmul⟩)
  have hB :
      B.card ≤ E₁.card + E₂.card + E₃.card := by
    calc
      B.card ≤ (E₁ ∪ E₂ ∪ E₃).card := Finset.card_le_card hsubset
      _ ≤ (E₁ ∪ E₂).card + E₃.card := Finset.card_union_le _ _
      _ ≤ (E₁.card + E₂.card) + E₃.card := by
        gcongr
        exact Finset.card_union_le _ _
  have hdist :
      SoficGroups.permutationDistance
        (completedRestriction r Z)
        (completedRestriction p Z * completedRestriction q Z) ≤ B.card := by
    calc
      SoficGroups.permutationDistance
          (completedRestriction r Z)
          (completedRestriction p Z * completedRestriction q Z) ≤
          (subtypeBad Z B).card :=
        permutationDistance_le_subtypeBad Z B _ _
          (fun x hx =>
            completedRestriction_mul_of_not_mem_restrictionMultiplicationBad
              p q r Z x hx)
      _ = (Z ∩ B).card := card_subtypeBad Z B
      _ ≤ B.card := Finset.card_le_card Finset.inter_subset_right
  have hE₁ : E₁.card ≤ (Finset.univ \ Z).card :=
    card_permutation_exit_le_deleted q Z
  have hE₂ : E₂.card ≤ (Finset.univ \ Z).card :=
    card_permutation_exit_le_deleted r Z
  change
    SoficGroups.permutationDistance
        (completedRestriction r Z)
        (completedRestriction p Z * completedRestriction q Z) ≤
      E₃.card + 2 * (Finset.univ \ Z).card
  omega
end SoficGroups.KunActualTwicePrunedFirstFactorRootBad
