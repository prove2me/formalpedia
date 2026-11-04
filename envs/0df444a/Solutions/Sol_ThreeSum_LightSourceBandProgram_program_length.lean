-- Prove2me | solution 1 for ThreeSum.LightSourceBandProgram.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:13:04.519946+00:00
-- url     : https://prove2.me/submissions/f5d4adcc-90b0-4af0-9850-4c7358c89491

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
import Definitions.Def_Submission_ThreeSum_LightSourceBandProgram

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandProgram
open Light
namespace ThreeSum.LightSourceBandProgram
theorem _root_.solution : program.length=13 := rfl
end ThreeSum.LightSourceBandProgram
