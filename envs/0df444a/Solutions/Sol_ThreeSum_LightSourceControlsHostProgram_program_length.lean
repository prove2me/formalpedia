-- Prove2me | solution 1 for ThreeSum.LightSourceControlsHostProgram.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:53:24.317879+00:00
-- url     : https://prove2.me/submissions/2fb08ff3-d2fb-4a6c-aa78-cc94c1ecc38f

import Definitions.Def_Submission_ThreeSum_LightSourceControlsHost
import Definitions.Def_Submission_ThreeSum_LightSourceControlsHostProgram

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceControlsHostProgram
open Light
namespace ThreeSum.LightSourceControlsHostProgram
theorem _root_.solution : program.length=80 := rfl
end ThreeSum.LightSourceControlsHostProgram
