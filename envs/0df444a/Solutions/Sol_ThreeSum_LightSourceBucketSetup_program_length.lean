-- Prove2me | solution 1 for ThreeSum.LightSourceBucketSetup.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:45:24.293789+00:00
-- url     : https://prove2.me/submissions/c660e277-d732-45a7-9d7a-c4ba27f35300

import Definitions.Def_Submission_ThreeSum_LightSourceBucketBuild
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_LightSourceBucketSetup

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketSetup
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBucketSetup
theorem _root_.solution : program.length = 7 := rfl
end ThreeSum.LightSourceBucketSetup
