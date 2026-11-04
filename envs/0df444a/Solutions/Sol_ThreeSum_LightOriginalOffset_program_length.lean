-- Prove2me | solution 1 for ThreeSum.LightOriginalOffset.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:47:01.615419+00:00
-- url     : https://prove2.me/submissions/1c5e904c-8923-4e53-a193-324eef2458f5

import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Definitions.Def_Submission_ThreeSum_LightOriginalOffset

set_option autoImplicit false
open ThreeSum ThreeSum.LightOriginalOffset
open Light LightResidues LightResidueHistogram
open KaratsubaInterface CyclicFold
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightOriginalOffset
theorem _root_.solution : program.length = 13 := rfl
end ThreeSum.LightOriginalOffset
