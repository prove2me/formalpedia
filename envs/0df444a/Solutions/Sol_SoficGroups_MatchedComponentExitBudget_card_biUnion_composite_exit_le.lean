-- Prove2me | solution 1 for SoficGroups.MatchedComponentExitBudget.card_biUnion_composite_exit_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/ac7f5807-1dfb-41af-8ee0-54c4881457e8

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MatchedComponentExitBudget_card_composite_exit_le_deleted

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentExitBudget
open Filter Topology
open scoped BigOperators
namespace SoficGroups.MatchedComponentExitBudget
theorem _root_.solution
    {V ι κ : Type*} [Fintype V] [DecidableEq V]
    (I : Finset ι) (K : Finset κ)
    (p : ι → Equiv.Perm V) (q : κ → Equiv.Perm V)
    (Z : Finset V) :
    (I.biUnion fun i =>
      K.biUnion fun k => Z.filter fun x => q k (p i x) ∉ Z).card ≤
        I.card * K.card * (Finset.univ \ Z).card := by
  classical
  calc
    (I.biUnion fun i =>
      K.biUnion fun k => Z.filter fun x => q k (p i x) ∉ Z).card ≤
        ∑ i ∈ I,
          (K.biUnion fun k => Z.filter fun x => q k (p i x) ∉ Z).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, K.card * (Finset.univ \ Z).card := by
      apply Finset.sum_le_sum
      intro i _
      calc
        (K.biUnion fun k =>
          Z.filter fun x => q k (p i x) ∉ Z).card ≤
            ∑ k ∈ K, (Z.filter fun x => q k (p i x) ∉ Z).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _k ∈ K, (Finset.univ \ Z).card := by
          apply Finset.sum_le_sum
          intro k _
          exact card_composite_exit_le_deleted (q k) (p i) Z
        _ = K.card * (Finset.univ \ Z).card := by simp
    _ = I.card * K.card * (Finset.univ \ Z).card := by
      simp [Nat.mul_assoc]
end SoficGroups.MatchedComponentExitBudget
