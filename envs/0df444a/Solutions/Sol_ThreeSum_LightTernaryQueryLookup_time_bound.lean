-- Prove2me | solution 1 for ThreeSum.LightTernaryQueryLookup.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:41:39.781368+00:00
-- url     : https://prove2.me/submissions/c8442c14-d6c3-4e38-926d-8cab3b1f9a21

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryQueryLookup
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryQueryLookup
theorem _root_.solution (L : ℕ) : time L ≤ 300*(L+1) := by
  unfold time LightBandLookup.searchTime
  omega
end ThreeSum.LightTernaryQueryLookup
