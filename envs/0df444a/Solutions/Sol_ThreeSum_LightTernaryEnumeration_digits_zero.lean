-- Prove2me | solution 1 for ThreeSum.LightTernaryEnumeration.digits_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:42:45.689002+00:00
-- url     : https://prove2.me/submissions/811a0198-daf1-4811-a1bb-9684f55c4189

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEnumeration
open Light ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryEnumeration
theorem _root_.solution : digits 0 = [0] := by norm_num [digits,List.range_succ]
end ThreeSum.LightTernaryEnumeration
