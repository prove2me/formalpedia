-- Prove2me | solution 1 for ThreeSum.TernaryCoverGoodMaps.prunedHit_le_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:55:22.706543+00:00
-- url     : https://prove2.me/submissions/c85494e7-443f-4989-acb4-db76cfc00294

import Definitions.Def_Submission_ThreeSum_TernaryCoverActualMoment
import Definitions.Def_Submission_ThreeSum_Cover
import Definitions.Def_Submission_ThreeSum_TernaryCoverGoodMaps

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverGoodMaps
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open TernaryLocalParameters TernaryCoverActualMoment TernaryCoverMoments
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]
namespace ThreeSum.TernaryCoverGoodMaps
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
end ThreeSum.TernaryCoverGoodMaps
