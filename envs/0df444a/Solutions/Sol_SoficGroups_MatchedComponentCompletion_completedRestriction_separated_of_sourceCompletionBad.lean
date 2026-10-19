-- Prove2me | solution 1 for SoficGroups.MatchedComponentCompletion.completedRestriction_separated_of_sourceCompletionBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/070d7324-3c5a-4069-9317-070c648ecf93

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_card_lt_five_mul_permutationDistance_of_subtypeBad
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_card_subtype_sourceCompletionBad
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_completedRestriction_ne_of_not_mem_sourceCompletionBad

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
    (F : Finset J) (Z : Finset V) (hZ : Z.Nonempty)
    (hbad : 5 * (sourceCompletionBad σ p F Z).card ≤ Z.card)
    {j k : J} (hj : j ∈ F) (hk : k ∈ F) (hne : j ≠ k) :
    Fintype.card {x : V // x ∈ Z} <
      5 * SoficGroups.permutationDistance
        (completedRestriction (p j) Z) (completedRestriction (p k) Z) := by
  apply card_lt_five_mul_permutationDistance_of_subtypeBad
    Z (sourceCompletionBad σ p F Z) hZ
  · simpa only [card_subtype_sourceCompletionBad, Fintype.card_coe]
      using hbad
  · intro z hz
    exact completedRestriction_ne_of_not_mem_sourceCompletionBad
      σ p F Z hj hk hne z hz
end SoficGroups.MatchedComponentCompletion
