-- Prove2me | solution 1 for ThreeSum.LightSubsetEnumerationSetup.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:37:00.981243+00:00
-- url     : https://prove2.me/submissions/4fec122a-ee82-460a-b91c-d0c763d8e29d

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetEnumerationSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSubsetEnumerationSetup
theorem _root_.solution (L k : ℕ) : time L k ≤ 800*(L+1)*(L.choose k+1) := by
  have h := LightSubsetEnumeration.time_bound L k
  unfold time powTableTime
  nlinarith
end ThreeSum.LightSubsetEnumerationSetup
