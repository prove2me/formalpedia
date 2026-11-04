-- Prove2me | solution 1 for ThreeSum.LightCacheEnumeration.pow_two_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:00:50.957826+00:00
-- url     : https://prove2.me/submissions/848e4653-db2e-47a2-8f71-416b2b9d7d4c

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_LightEnumeration

set_option autoImplicit false
open ThreeSum ThreeSum.LightCacheEnumeration
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
open Light ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightCacheEnumeration
theorem _root_.solution (N : ℕ) : 2^(2*N) = 4^N := by
  rw [pow_mul]
  norm_num
end ThreeSum.LightCacheEnumeration
