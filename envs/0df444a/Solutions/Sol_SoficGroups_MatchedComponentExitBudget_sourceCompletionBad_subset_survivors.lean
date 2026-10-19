-- Prove2me | solution 1 for SoficGroups.MatchedComponentExitBudget.sourceCompletionBad_subset_survivors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/2b36dc2f-250f-4a61-900f-773de83a294d

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentExitBudget
open Filter Topology
open scoped BigOperators
namespace SoficGroups.MatchedComponentExitBudget
theorem _root_.solution
    {V ι J : Type*} [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V) :
    SoficGroups.MatchedComponentCompletion.sourceCompletionBad
      σ p F Z ⊆ Z := by
  classical
  intro x hx
  simp [SoficGroups.MatchedComponentCompletion.sourceCompletionBad] at hx
  aesop
end SoficGroups.MatchedComponentExitBudget
