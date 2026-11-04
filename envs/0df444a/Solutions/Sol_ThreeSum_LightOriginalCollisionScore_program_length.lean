-- Prove2me | solution 1 for ThreeSum.LightOriginalCollisionScore.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:49:27.082201+00:00
-- url     : https://prove2.me/submissions/cd3cdac6-a57e-4e4b-b1b5-f5db37a4e52b

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionScore

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalCollisionScore
open Light Finset
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightOriginalCollisionScore
theorem _root_.solution : program.length=4 := rfl
end ThreeSum.LightOriginalCollisionScore
