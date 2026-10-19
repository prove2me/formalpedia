-- Prove2me | solution 1 for SoficGroups.SourceCommonComponentComparisonBad.comparisonBad_card_le_overlap_and_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/118f5f78-0c65-48a3-910f-f30c4b7e855e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_matchedWordPreimageBad_card_le
import Theorems.Thm_SoficGroups_SourceCommonComponentComparisonBad_comparisonBad_subset_matchedWordPreimageBad
import Theorems.Thm_SoficGroups_SourceCommonComponentComparisonBad_matchedCore_missing_card_le_overlap_and_loss

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
    (comparisonBad Q T eta).card ≤
      (∑ C ∈ SoficGroups.insufficientOverlapComponents
        (SoficGroups.transportedUnivFinpartition Q T) Q eta,
          C.card) +
      ∑ C ∈ (SoficGroups.transportedUnivFinpartition Q T).parts,
        (C \
          SoficGroups.maximumOverlapPart Q C).card := by
  calc
    (comparisonBad Q T eta).card ≤
        (SoficGroups.matchedWordPreimageBad
          (Finset.univ : Finset V)
          (overlapRetainedComponents Q T eta)
          (SoficGroups.maximumOverlapPart Q) T).card :=
      Finset.card_le_card
        (comparisonBad_subset_matchedWordPreimageBad Q T eta)
    _ ≤ ((Finset.univ : Finset V) \
          SoficGroups.matchedCore
            (overlapRetainedComponents Q T eta)
            (SoficGroups.maximumOverlapPart Q)).card :=
      SoficGroups.matchedWordPreimageBad_card_le
        (Finset.univ : Finset V)
        (overlapRetainedComponents Q T eta)
        (SoficGroups.maximumOverlapPart Q) T
    _ ≤ _ := matchedCore_missing_card_le_overlap_and_loss Q T eta
end SoficGroups.SourceCommonComponentComparisonBad
