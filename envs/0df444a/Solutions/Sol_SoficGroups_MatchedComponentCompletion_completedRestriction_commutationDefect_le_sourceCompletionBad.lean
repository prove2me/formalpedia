-- Prove2me | solution 1 for SoficGroups.MatchedComponentCompletion.completedRestriction_commutationDefect_le_sourceCompletionBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/f0f7e339-9372-45c5-b196-056bfc6df9bf

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_card_subtype_sourceCompletionBad
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_completedRestriction_commute_of_not_mem_sourceCompletionBad

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
    (σZ : ι → Equiv.Perm {x : V // x ∈ Z})
    (hσZ : ∀ i (x : V) (hx : x ∈ Z) (_hi : σ i x ∈ Z),
      ((σZ i ⟨x, hx⟩ : {x : V // x ∈ Z}) : V) = σ i x)
    {j : J}
    (hj : j ∈ SoficGroups.CompressionCriterion.productTrackedTable F) :
    SoficGroups.permutationCommutationDefect
        σZ (completedRestriction (p j) Z) ≤
      Fintype.card ι * (sourceCompletionBad σ p F Z).card := by
  classical
  unfold SoficGroups.permutationCommutationDefect
  calc
    (∑ i : ι,
      (Finset.univ.filter fun x : {x : V // x ∈ Z} =>
        completedRestriction (p j) Z (σZ i x) ≠
          σZ i (completedRestriction (p j) Z x)).card) ≤
        ∑ _i : ι, (subtypeBad Z (sourceCompletionBad σ p F Z)).card := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.card_le_card
          intro x hx
          apply (mem_subtypeBad Z (sourceCompletionBad σ p F Z) x).2
          by_contra hnot
          exact (Finset.mem_filter.mp hx).2
            (completedRestriction_commute_of_not_mem_sourceCompletionBad
              σ p F Z σZ hσZ hj i x hnot)
    _ = Fintype.card ι * (sourceCompletionBad σ p F Z).card := by
      simp [card_subtype_sourceCompletionBad]
end SoficGroups.MatchedComponentCompletion
