-- Prove2me | solution 1 for ThreeSum.LightBandEnumeration.count_eq_owner_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:44.689444+00:00
-- url     : https://prove2.me/submissions/bbd00010-7f7a-478f-bdd7-add40a6fd2fb

import Definitions.Def_Submission_ThreeSum_LightBandTable
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_LightCapacity
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Theorems.Thm_ThreeSum_BandEnumeration_owners_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandEnumeration
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandEnumeration
theorem _root_.solution (A B C : Family) :
    count A.size B.size C.size = (owners A B C).length := by
  rw [owners_length]
  unfold count
  ring
end ThreeSum.LightBandEnumeration
