-- Prove2me | solution 1 for ThreeSum.LightGlobalKeys.localCount_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:23:31.42531+00:00
-- url     : https://prove2.me/submissions/55d2c589-cf7c-4ce3-8598-b5a2e97f89b6

import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightGlobalKeys

set_option autoImplicit false
open ThreeSum ThreeSum.LightGlobalKeys
open Light GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open LightSubsetAddress SubsetAddress
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
namespace ThreeSum.LightGlobalKeys
theorem _root_.solution (h : ℕ) : 0 < localCount h := by
  apply Nat.mul_pos
  · unfold scheduleSize scheduleLength
    positivity
  · exact Nat.choose_pos (by omega)
end ThreeSum.LightGlobalKeys
