-- Prove2me | solution 1 for ThreeSum.LightEncodedColorResult.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:07:18.470586+00:00
-- url     : https://prove2.me/submissions/27e2ee35-a2a2-4c7b-a9de-7ed0fef900ee

import Definitions.Def_Submission_ThreeSum_EncodedColorSourceRetention
import Definitions.Def_Submission_ThreeSum_LightEncodedColorResult

set_option autoImplicit false
open ThreeSum ThreeSum.LightEncodedColorResult
open Light
namespace ThreeSum.LightEncodedColorResult
theorem _root_.solution : program.length=1 := rfl
end ThreeSum.LightEncodedColorResult
