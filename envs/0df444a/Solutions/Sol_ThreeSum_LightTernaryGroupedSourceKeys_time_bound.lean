-- Prove2me | solution 1 for ThreeSum.LightTernaryGroupedSourceKeys.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:41:43.300486+00:00
-- url     : https://prove2.me/submissions/49dd0ad3-73b3-4243-a391-a506a9af223b

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedSourceKeys

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryGroupedSourceKeys
open Light ThreeSum.LightSubsetAddress
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryGroupedSourceKeys
theorem _root_.solution (L count : ℕ) : time L count ≤ 500*(L+1)*(count+1) := by
  unfold time LightBandLookup.searchTime
  nlinarith
end ThreeSum.LightTernaryGroupedSourceKeys
