-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverGoodMaps.prunedHit_le_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:11:42.086451+00:00
-- url     : https://prove2.me/submissions/2a8805fc-b22e-47f0-b295-5c535225e928

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverActualMoment
import Definitions.Def_Submission_ThreeSum_Cover
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverGoodMaps

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverGoodMaps
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open WeightedGlobalLocalParameters WeightedGlobalCoverActualMoment TernaryCoverMoments
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverGoodMaps
theorem _root_.solution (B τ : ℕ) (w : Weight m p) (a b : ZMod p) :
    prunedHit m p B τ w a b ≤ TernaryCoverFibers.rawPairCount
      (leftHash (α := fixedAlpha m) (π := fixedPi m) w) (rightHash w) a b := by
  classical
  unfold prunedHit
  split_ifs
  · exact Nat.zero_le _
  · apply card_le_card
    intro e he
    have ht := (mem_filter.mp he).2
    have hpair := (mem_filter.mp (mem_filter.mp ht).1).2
    exact mem_filter.mpr ⟨mem_univ _, hpair⟩
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverGoodMaps
