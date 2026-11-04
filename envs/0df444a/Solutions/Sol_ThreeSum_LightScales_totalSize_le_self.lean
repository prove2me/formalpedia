-- Prove2me | solution 1 for ThreeSum.LightScales.totalSize_le_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:14:11.117712+00:00
-- url     : https://prove2.me/submissions/7d14dc34-dfe4-449d-95d1-55ccc03443ca

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightScales
import Theorems.Thm_ThreeSum_Scales_totalSize_upper


set_option autoImplicit false
open ThreeSum ThreeSum.LightScales
open Light ThreeSum.Scales
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightScales
theorem _root_.solution (m : ℕ) : totalSize m ≤ m := by
  have h := totalSize_upper m
  omega
end ThreeSum.LightScales
