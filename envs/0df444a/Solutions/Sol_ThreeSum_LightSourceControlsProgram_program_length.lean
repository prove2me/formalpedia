-- Prove2me | solution 1 for ThreeSum.LightSourceControlsProgram.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:41:26.353196+00:00
-- url     : https://prove2.me/submissions/883c0eed-50fd-47a8-b7da-51a9d1c64948

import Definitions.Def_Submission_ThreeSum_LightSourceControls
import Definitions.Def_Submission_ThreeSum_LightSourceControlsProgram

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceControlsProgram
open Light
namespace ThreeSum.LightSourceControlsProgram
theorem _root_.solution : program.length=14 := rfl
end ThreeSum.LightSourceControlsProgram
