-- Prove2me | solution 1 for SoficGroups.MatchedComponentExitBudget.card_composite_exit_le_deleted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/2f60d5b8-3e8c-4e54-9f09-dc5bfe161cee

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
    (p q : Equiv.Perm V) (Z : Finset V) :
    (Z.filter fun x => p (q x) ∉ Z).card ≤
      (Finset.univ \ Z).card := by
  apply Finset.card_le_card_of_injOn (p * q)
  · intro x hx
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [Equiv.Perm.mul_apply] using (Finset.mem_filter.mp hx).2
  · exact (p * q).injective.injOn
end SoficGroups.MatchedComponentExitBudget
