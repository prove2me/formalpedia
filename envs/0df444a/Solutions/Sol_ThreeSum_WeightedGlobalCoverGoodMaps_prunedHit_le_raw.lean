-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverGoodMaps.prunedHit_le_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:07:02.000488+00:00
-- url     : https://prove2.me/submissions/368b6204-1487-4a3f-af78-1ab459c6b79a

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverActualMoment
import Definitions.Def_Submission_ThreeSum_Cover
import Definitions.Def_Submission_Weighted_Global_TernaryCoverGoodMaps

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverGoodMaps
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open WeightedGlobalLocalParameters WeightedGlobalCoverActualMoment TernaryCoverMoments
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]
namespace ThreeSum.WeightedGlobalCoverGoodMaps
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
end ThreeSum.WeightedGlobalCoverGoodMaps
