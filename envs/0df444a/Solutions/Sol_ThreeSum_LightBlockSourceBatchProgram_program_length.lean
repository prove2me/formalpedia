-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchProgram.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:09.503195+00:00
-- url     : https://prove2.me/submissions/d3aeace8-56c5-4d37-9d82-0d2c0a1850f3

import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatch
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedProgram
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchProgram

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatchProgram
open Light SubsetAddress
set_option maxHeartbeats 1800000
set_option maxRecDepth 14000
namespace ThreeSum.LightBlockSourceBatchProgram
theorem _root_.solution : program.length=43 := rfl
end ThreeSum.LightBlockSourceBatchProgram
