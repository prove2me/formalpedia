-- Prove2me | solution 1 for ThreeSum.LightTernaryEnumeration.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:37:12.701743+00:00
-- url     : https://prove2.me/submissions/3f42858b-7562-4baf-b990-82f88407a637

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_visits_le_codes


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEnumeration
open Light ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryEnumeration
theorem _root_.solution (N T : ℕ) :
    time N T ≤ 300*((N+1)*(codes N T).length) := by
  exact Nat.mul_le_mul_left 300 (visits_le_codes N T)
end ThreeSum.LightTernaryEnumeration
