-- Prove2me | solution 1 for SoficGroups.MatchedComponentCompletion.completedRestriction_mul_distance_le_sourceCompletionBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/528dba09-7fa9-4f25-9f05-7ef63e9d592b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_permutationDistance_le_subtypeBad
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_card_subtype_sourceCompletionBad
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_completedRestriction_mul_of_not_mem_sourceCompletionBad

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentCompletion
open scoped BigOperators
namespace SoficGroups.MatchedComponentCompletion
theorem _root_.solution
    {V ι J : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V)
    {j k : J} (hj : j ∈ F) (hk : k ∈ F) :
    SoficGroups.permutationDistance
      (completedRestriction (p (j * k)) Z)
      (completedRestriction (p j) Z * completedRestriction (p k) Z) ≤
        (sourceCompletionBad σ p F Z).card := by
  calc
    SoficGroups.permutationDistance
      (completedRestriction (p (j * k)) Z)
      (completedRestriction (p j) Z * completedRestriction (p k) Z) ≤
        (subtypeBad Z (sourceCompletionBad σ p F Z)).card := by
          apply permutationDistance_le_subtypeBad
          intro z hz
          exact completedRestriction_mul_of_not_mem_sourceCompletionBad
            σ p F Z hj hk z hz
    _ = (sourceCompletionBad σ p F Z).card :=
      card_subtype_sourceCompletionBad σ p F Z
end SoficGroups.MatchedComponentCompletion
