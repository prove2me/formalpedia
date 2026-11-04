-- Prove2me | solution 1 for ThreeSum.LightTernaryFinalPreparation.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:57:01.64158+00:00
-- url     : https://prove2.me/submissions/8d89e423-1189-45a2-82ad-792d881428e8

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionScore
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightTernaryFinalPreparation

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryFinalPreparation
open Light LightSubsetAddress
set_option maxHeartbeats 3000000
set_option maxRecDepth 12000
variable {lim : Limits}
namespace ThreeSum.LightTernaryFinalPreparation
theorem _root_.solution : program.length = 6 := rfl
end ThreeSum.LightTernaryFinalPreparation
