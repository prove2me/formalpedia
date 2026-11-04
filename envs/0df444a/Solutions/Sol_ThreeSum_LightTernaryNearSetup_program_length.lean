-- Prove2me | solution 1 for ThreeSum.LightTernaryNearSetup.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:21:33.716141+00:00
-- url     : https://prove2.me/submissions/39123cc7-09ff-48da-b20c-bec1b0178f15

import Definitions.Def_Submission_ThreeSum_LightTernaryNearDigits
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumerationMain
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
import Definitions.Def_Submission_ThreeSum_LightTernaryNearSetup

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearSetup
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBankEnumeration ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryNearSetup
theorem _root_.solution : program.length=7 := rfl
end ThreeSum.LightTernaryNearSetup
