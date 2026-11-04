-- Prove2me | solution 1 for ThreeSum.LightSourceBandHostProgram.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:41:07.592378+00:00
-- url     : https://prove2.me/submissions/43604ace-a2b7-4bf3-a88e-15f4317ab27a

import Definitions.Def_Submission_ThreeSum_LightSourceBandHost
import Definitions.Def_Submission_ThreeSum_LightSourceBandHostProgram

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandHostProgram
open Light
namespace ThreeSum.LightSourceBandHostProgram
theorem _root_.solution : program.length=65 := rfl
end ThreeSum.LightSourceBandHostProgram
