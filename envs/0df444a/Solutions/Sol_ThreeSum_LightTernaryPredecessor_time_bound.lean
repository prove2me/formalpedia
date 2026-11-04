-- Prove2me | solution 1 for ThreeSum.LightTernaryPredecessor.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:53:17.793617+00:00
-- url     : https://prove2.me/submissions/2ed10818-8180-4fc7-97c1-8d15a286ba16

import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessor

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPredecessor
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
open ThreeSum.TernaryEuler
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryPredecessor
theorem _root_.solution (N L : ℕ) : time N L≤3000*(N+L+1)^2 := by
  unfold time LightTernaryRank.time LightTernaryCodes.digitTime
    LightTernaryCodes.zeroTime LightMaskErase.time LightBandLookup.searchTime
  nlinarith
end ThreeSum.LightTernaryPredecessor
