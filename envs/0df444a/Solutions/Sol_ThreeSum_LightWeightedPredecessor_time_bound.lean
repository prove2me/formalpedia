-- Prove2me | solution 1 for ThreeSum.LightWeightedPredecessor.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:53:12.453045+00:00
-- url     : https://prove2.me/submissions/0bacb0d5-f3bf-4317-8b33-76257121e8ee

import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
import Definitions.Def_Submission_Weighted_LightCost
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Predecessor

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedPredecessor
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
open ThreeSum.TernaryEuler
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedPredecessor
theorem _root_.solution (N L : ℕ) : time N L≤3000*(N+L+1)^2 := by
  unfold time LightWeightedCost.time LightTernaryCodes.digitTime
    LightTernaryCodes.zeroTime LightMaskErase.time LightBandLookup.searchTime
  nlinarith
end ThreeSum.LightWeightedPredecessor
