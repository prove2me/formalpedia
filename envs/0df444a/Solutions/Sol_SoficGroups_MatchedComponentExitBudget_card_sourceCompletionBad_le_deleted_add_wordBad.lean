-- Prove2me | solution 1 for SoficGroups.MatchedComponentExitBudget.card_sourceCompletionBad_le_deleted_add_wordBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/ecab46f7-7f49-4939-ad5c-d29dd6caa99d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MatchedComponentExitBudget_card_biUnion_permutation_exit_le
import Theorems.Thm_SoficGroups_MatchedComponentExitBudget_card_biUnion_composite_exit_le
import Theorems.Thm_SoficGroups_MatchedComponentExitBudget_sourceCompletionBad_subset_exit_union_wordBad

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentExitBudget
open Filter Topology
open scoped BigOperators
namespace SoficGroups.MatchedComponentExitBudget
theorem _root_.solution
    {V ι J : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V) :
    (SoficGroups.MatchedComponentCompletion.sourceCompletionBad
      σ p F Z).card ≤
        (Fintype.card ι +
          (SoficGroups.CompressionCriterion.productTrackedTable F).card +
          Fintype.card ι *
            (SoficGroups.CompressionCriterion.productTrackedTable F).card) *
          (Finset.univ \ Z).card +
        (sourceWordTestBad σ p F).card := by
  classical
  let I : Finset ι := Finset.univ
  let T : Finset J :=
    SoficGroups.CompressionCriterion.productTrackedTable F
  let A : Finset V :=
    I.biUnion fun i => Z.filter fun z => σ i z ∉ Z
  let D : Finset V :=
    T.biUnion fun j => Z.filter fun z => p j z ∉ Z
  let C : Finset V :=
    I.biUnion fun i =>
      T.biUnion fun j => Z.filter fun z => p j (σ i z) ∉ Z
  let W : Finset V := sourceWordTestBad σ p F
  let deleted : Finset V := Finset.univ \ Z
  have hA : A.card ≤ Fintype.card ι * deleted.card := by
    simpa [A, I, deleted] using
      card_biUnion_permutation_exit_le
        (Finset.univ : Finset ι) σ Z
  have hD : D.card ≤ T.card * deleted.card := by
    simpa [D, deleted] using
      card_biUnion_permutation_exit_le T p Z
  have hC : C.card ≤ Fintype.card ι * T.card * deleted.card := by
    simpa [C, I, deleted] using
      card_biUnion_composite_exit_le
        (Finset.univ : Finset ι) T σ p Z
  have hsubset :
      SoficGroups.MatchedComponentCompletion.sourceCompletionBad
          σ p F Z ⊆ A ∪ D ∪ C ∪ W := by
    simpa [A, D, C, I, T, W] using
      sourceCompletionBad_subset_exit_union_wordBad σ p F Z
  have hunion :
      (A ∪ D ∪ C ∪ W).card ≤ A.card + D.card + C.card + W.card := by
    have hAD := Finset.card_union_le A D
    have hADC := Finset.card_union_le (A ∪ D) C
    have hADCW := Finset.card_union_le (A ∪ D ∪ C) W
    omega
  calc
    (SoficGroups.MatchedComponentCompletion.sourceCompletionBad
        σ p F Z).card ≤ (A ∪ D ∪ C ∪ W).card :=
      Finset.card_le_card hsubset
    _ ≤ A.card + D.card + C.card + W.card := hunion
    _ ≤ Fintype.card ι * deleted.card +
        T.card * deleted.card +
        Fintype.card ι * T.card * deleted.card + W.card := by
      omega
    _ = (Fintype.card ι +
          (SoficGroups.CompressionCriterion.productTrackedTable F).card +
          Fintype.card ι *
            (SoficGroups.CompressionCriterion.productTrackedTable F).card) *
          (Finset.univ \ Z).card +
        (sourceWordTestBad σ p F).card := by
      dsimp [T, deleted, W]
      ring
end SoficGroups.MatchedComponentExitBudget
