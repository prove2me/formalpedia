-- Prove2me | solution 1 for SoficGroups.MatchedComponentCompletion.sourceCompletionBad_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/e6e7e5d9-3c23-4aaf-ab14-b96bf038fe50

import Mathlib
import Definitions.Def_NonSoficGroup

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
    sourceCompletionBad σ p F Z ⊆ Z := by
  classical
  intro x hx
  simp [sourceCompletionBad] at hx
  aesop
end SoficGroups.MatchedComponentCompletion
