-- Prove2me | solution 1 for ThreeSum.LightLocalKeyRow.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:43:10.235677+00:00
-- url     : https://prove2.me/submissions/7ca9a597-f183-4351-97fc-8108fcfa152d

import Definitions.Def_Submission_ThreeSum_LightMaskHashes
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightLocalKeyRow
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalKeyRow
open Light LightSubsetAddress
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightLocalKeyRow
theorem _root_.solution (L n : ℕ) : time L n ≤ 950*(L+1)*(n+1) := by
  have h := LightMaskHashes.time_bound L n
  unfold time fillTime LightArray.linearTime
  nlinarith
end ThreeSum.LightLocalKeyRow
