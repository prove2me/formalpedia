-- Prove2me | solution 1 for ThreeSum.LightTernarySourceKeys.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:41:42.16725+00:00
-- url     : https://prove2.me/submissions/b3e52d75-2720-43e9-8e00-60763e9bc692

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightTernarySourceKeys

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernarySourceKeys
open Light ThreeSum.LightSubsetAddress
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernarySourceKeys
theorem _root_.solution (L count : ℕ) : time L count ≤ 500*(L+1)*(count+1) := by
  unfold time LightBandLookup.searchTime
  nlinarith
end ThreeSum.LightTernarySourceKeys
