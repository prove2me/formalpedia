-- Prove2me | solution 1 for ThreeSum.LightSourceBucketOriginal.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:40:14.158995+00:00
-- url     : https://prove2.me/submissions/4b84ffbf-eb84-4284-b968-2e9c6a1e4f0b

import Definitions.Def_Submission_ThreeSum_LightSourceBucketFromHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketOriginal
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBucketOriginal
theorem _root_.solution : program.length = 9 := rfl
end ThreeSum.LightSourceBucketOriginal
