-- Prove2me | solution 1 for ThreeSum.LightWeightedNearSetup.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:08:36.043424+00:00
-- url     : https://prove2.me/submissions/976fcf52-ca14-45ac-a0ee-14c2cb5dfc1b

import Definitions.Def_Submission_Weighted_NearDigits
import Definitions.Def_Submission_Weighted_LightNearEnumerationMain
import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearSetup

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedNearSetup
open Light ThreeSum.LightSubsetAddress
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.TernaryJointType ThreeSum.WeightedBankEnumeration ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedNearSetup
theorem _root_.solution : program.length=7 := rfl
end ThreeSum.LightWeightedNearSetup
