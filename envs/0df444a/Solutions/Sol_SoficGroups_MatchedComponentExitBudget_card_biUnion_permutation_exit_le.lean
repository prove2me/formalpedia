-- Prove2me | solution 1 for SoficGroups.MatchedComponentExitBudget.card_biUnion_permutation_exit_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/d1a931d7-fadd-4e04-8f8c-efa3b1f8ce71

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MatchedComponentExitBudget_card_permutation_exit_le_deleted

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentExitBudget
open Filter Topology
open scoped BigOperators
namespace SoficGroups.MatchedComponentExitBudget
theorem _root_.solution
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (I : Finset ι) (p : ι → Equiv.Perm V) (Z : Finset V) :
    (I.biUnion fun i => Z.filter fun x => p i x ∉ Z).card ≤
      I.card * (Finset.univ \ Z).card := by
  classical
  calc
    (I.biUnion fun i => Z.filter fun x => p i x ∉ Z).card ≤
        ∑ i ∈ I, (Z.filter fun x => p i x ∉ Z).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, (Finset.univ \ Z).card := by
      apply Finset.sum_le_sum
      intro i _
      exact card_permutation_exit_le_deleted (p i) Z
    _ = I.card * (Finset.univ \ Z).card := by simp
end SoficGroups.MatchedComponentExitBudget
