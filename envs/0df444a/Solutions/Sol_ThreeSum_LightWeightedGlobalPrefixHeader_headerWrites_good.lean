-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalPrefixHeader.headerWrites_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:42:19.33535+00:00
-- url     : https://prove2.me/submissions/18eacc2e-9cce-4ee2-91ac-52bb6ddb4e5d

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixLoop
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixHeader

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixHeader
open Light
open LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000
namespace ThreeSum.LightWeightedGlobalPrefixHeader
theorem _root_.solution : ∀ir∈headerWrites, ir.1<106 ∧ ir.2<30 := by decide
end ThreeSum.LightWeightedGlobalPrefixHeader
