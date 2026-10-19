-- Prove2me | solution 1 for SoficGroups.MatchedComponentExitBudget.card_permutation_exit_le_deleted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/3a9c2b01-37a2-4f2e-a428-009260f16bd0

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
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (Z : Finset V) :
    (Z.filter fun x => p x ∉ Z).card ≤
      (Finset.univ \ Z).card := by
  apply Finset.card_le_card_of_injOn p
  · intro x hx
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  · exact p.injective.injOn
end SoficGroups.MatchedComponentExitBudget
