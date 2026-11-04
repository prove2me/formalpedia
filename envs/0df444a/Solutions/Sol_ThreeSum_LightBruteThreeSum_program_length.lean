-- Prove2me | solution 1 for ThreeSum.LightBruteThreeSum.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:09:54.818932+00:00
-- url     : https://prove2.me/submissions/da1f8e72-3c39-4400-afdf-4086a537173f

import Definitions.Def_Submission_ThreeSum_LightOriginalTripleScan
import Definitions.Def_Submission_ThreeSum_OriginalThreeSum
import Definitions.Def_Submission_ThreeSum_LightBruteThreeSum

set_option autoImplicit false
open ThreeSum ThreeSum.LightBruteThreeSum
open Light ThreeSumApsp.Spec
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace ThreeSum.LightBruteThreeSum
theorem _root_.solution : program.length=4 := rfl
end ThreeSum.LightBruteThreeSum
