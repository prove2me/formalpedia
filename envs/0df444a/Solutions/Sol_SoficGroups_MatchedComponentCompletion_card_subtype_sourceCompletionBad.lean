-- Prove2me | solution 1 for SoficGroups.MatchedComponentCompletion.card_subtype_sourceCompletionBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/c1a4b59e-0c96-4ec2-bda8-ae8403699366

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_card_subtypeBad
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_sourceCompletionBad_subset

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentCompletion
open scoped BigOperators
namespace SoficGroups.MatchedComponentCompletion
theorem _root_.solution
    {V ι J : Type*} [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V) :
    (subtypeBad Z (sourceCompletionBad σ p F Z)).card =
      (sourceCompletionBad σ p F Z).card := by
  rw [card_subtypeBad, Finset.inter_eq_right.mpr]
  exact sourceCompletionBad_subset σ p F Z
end SoficGroups.MatchedComponentCompletion
