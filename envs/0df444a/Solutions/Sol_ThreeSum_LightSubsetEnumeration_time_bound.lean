-- Prove2me | solution 1 for ThreeSum.LightSubsetEnumeration.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:31:25.201715+00:00
-- url     : https://prove2.me/submissions/bc4a7b85-9bae-49bb-9472-b683c999a342

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_WeightedCache3SUM_Alias_85ca0f35704fc2ef


set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSubsetEnumeration
theorem _root_.solution (L k : ℕ) :
    time L k ≤ 150*((4*L+1)*L.choose k+1) := by
  exact Nat.mul_le_mul_left 150 (enumerationWork_bound L k)
end ThreeSum.LightSubsetEnumeration
