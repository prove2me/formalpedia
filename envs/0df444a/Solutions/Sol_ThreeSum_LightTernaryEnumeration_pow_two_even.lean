-- Prove2me | solution 1 for ThreeSum.LightTernaryEnumeration.pow_two_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:36:05.421167+00:00
-- url     : https://prove2.me/submissions/0f0ddf3f-47fe-409e-b050-5f99f699b659

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEnumeration
open Light ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryEnumeration
theorem _root_.solution (N : ℕ) : 2^(2*N) = 4^N := by
  rw [pow_mul]
  norm_num
end ThreeSum.LightTernaryEnumeration
