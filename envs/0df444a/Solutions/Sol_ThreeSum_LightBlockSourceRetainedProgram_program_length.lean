-- Prove2me | solution 1 for ThreeSum.LightBlockSourceRetainedProgram.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:14:22.01214+00:00
-- url     : https://prove2.me/submissions/28cb4b7c-e351-4ddd-aa3a-6d67676f46c3

import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedHost
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedProgram

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceRetainedProgram
open Light LightPascal LightSubsetAddress LightBlockSourceRetainedHost
open LocalCoverBounds SubsetAddress BlockSourceEncoding LightBlockSourceBuild
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
namespace ThreeSum.LightBlockSourceRetainedProgram
theorem _root_.solution : program.length = 41 := rfl
end ThreeSum.LightBlockSourceRetainedProgram
