-- Prove2me | solution 1 for ThreeSum.LightSourceBucketBuild.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:39:57.25349+00:00
-- url     : https://prove2.me/submissions/c0224646-89f9-487e-8aaa-58efcd692995

import Definitions.Def_Submission_ThreeSum_LightSourceBucketFromHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceBucketBuild

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketBuild
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBucketBuild
theorem _root_.solution : program.length = 6 := rfl
end ThreeSum.LightSourceBucketBuild
