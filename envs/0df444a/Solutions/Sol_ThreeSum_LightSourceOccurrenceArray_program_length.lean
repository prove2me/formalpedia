-- Prove2me | solution 1 for ThreeSum.LightSourceOccurrenceArray.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:21:45.952589+00:00
-- url     : https://prove2.me/submissions/c4e9654f-47ee-4251-99fd-c59d0e7e584a

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_LightSourceOccurrenceArray

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceOccurrenceArray
open Light OutputDecodeOrder
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceOccurrenceArray
theorem _root_.solution : program.length=3 := rfl
end ThreeSum.LightSourceOccurrenceArray
