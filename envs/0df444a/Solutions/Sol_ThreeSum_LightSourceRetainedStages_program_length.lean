-- Prove2me | solution 1 for ThreeSum.LightSourceRetainedStages.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:52:23.271089+00:00
-- url     : https://prove2.me/submissions/b35269be-6e85-474a-bd9c-94b0ccdaf4bd

import Definitions.Def_Submission_ThreeSum_LightSourceStages
import Definitions.Def_Submission_ThreeSum_LightSourceRetainedStages

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceRetainedStages
open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceRetainedStages
theorem _root_.solution : program.length = 19 := rfl
end ThreeSum.LightSourceRetainedStages
