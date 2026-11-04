-- Prove2me | solution 1 for ThreeSum.LightDownsetAddress.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:39:14.476794+00:00
-- url     : https://prove2.me/submissions/da3014bc-0d91-49b1-b04d-8f73d52fb47a

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_LightDownsetAddress
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetAddress
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightDownsetAddress
theorem _root_.solution (L : ℕ) : time L ≤ 1300*(L+1)^2 := by
  have h := LightSubsetSetup.time_bound L
  unfold time LightSubsetOffset.time
  nlinarith
end ThreeSum.LightDownsetAddress
