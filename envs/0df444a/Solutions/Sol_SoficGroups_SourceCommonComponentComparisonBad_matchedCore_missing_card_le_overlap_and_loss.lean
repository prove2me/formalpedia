-- Prove2me | solution 1 for SoficGroups.SourceCommonComponentComparisonBad.matchedCore_missing_card_le_overlap_and_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/4f4434ba-f2e8-4138-9394-7b61abc4f539

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_matchedRetainedSupport_subset
import Theorems.Thm_SoficGroups_matchedRetainedSupport_card
import Theorems.Thm_SoficGroups_matchedCore_missing_card
import Theorems.Thm_SoficGroups_insufficientOverlapComponents_subset

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCommonComponentComparisonBad
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceCommonComponentComparisonBad
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (eta : ℝ) :
    ((Finset.univ : Finset V) \
      SoficGroups.matchedCore
        (overlapRetainedComponents Q T eta)
        (SoficGroups.maximumOverlapPart Q)).card ≤
      (∑ C ∈ SoficGroups.insufficientOverlapComponents
        (SoficGroups.transportedUnivFinpartition Q T) Q eta,
          C.card) +
      ∑ C ∈ (SoficGroups.transportedUnivFinpartition Q T).parts,
        (C \
          SoficGroups.maximumOverlapPart Q C).card := by
  classical
  let P := SoficGroups.transportedUnivFinpartition Q T
  let O := SoficGroups.insufficientOverlapComponents P Q eta
  let R := P.parts \
    SoficGroups.insufficientOverlapComponents P Q eta
  have hR : R ⊆ P.parts := Finset.sdiff_subset
  have hO : O ⊆ P.parts :=
    SoficGroups.insufficientOverlapComponents_subset P Q eta
  have hparts : P.parts \ R = O := by
    ext C
    constructor
    · intro h
      obtain ⟨hCP, hnot⟩ := Finset.mem_sdiff.mp h
      by_contra hCO
      exact hnot (Finset.mem_sdiff.mpr ⟨hCP, hCO⟩)
    · intro h
      exact Finset.mem_sdiff.mpr
        ⟨hO h, fun hR' => (Finset.mem_sdiff.mp hR').2 h⟩
  have hmissing :
      ((Finset.univ : Finset V) \
        SoficGroups.matchedRetainedSupport R).card =
        ∑ C ∈ O, C.card := by
    have hsplit := Finset.sum_sdiff hR (f := fun C : Finset V => C.card)
    rw [hparts] at hsplit
    have hfull := P.sum_card_parts
    have hret := SoficGroups.matchedRetainedSupport_card P R hR
    have hcard := Finset.card_sdiff_add_card_eq_card
      (SoficGroups.matchedRetainedSupport_subset P R hR)
    omega
  change
    ((Finset.univ : Finset V) \
      SoficGroups.matchedCore R
        (SoficGroups.maximumOverlapPart Q)).card ≤
      (∑ C ∈ O, C.card) +
        ∑ C ∈ P.parts,
          (C \ SoficGroups.maximumOverlapPart Q C).card
  rw [SoficGroups.matchedCore_missing_card P R hR
    (SoficGroups.maximumOverlapPart Q), hmissing]
  apply Nat.add_le_add_left
  exact Finset.sum_le_sum_of_subset_of_nonneg hR
    (fun _ _ _ => Nat.zero_le _)
end SoficGroups.SourceCommonComponentComparisonBad
