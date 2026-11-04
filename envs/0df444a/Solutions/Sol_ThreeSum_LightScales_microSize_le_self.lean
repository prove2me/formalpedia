-- Prove2me | solution 1 for ThreeSum.LightScales.microSize_le_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:37:06.876683+00:00
-- url     : https://prove2.me/submissions/ac25d6d0-339e-4f68-ab5d-7da1bbc8ec3e

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightScales
import Theorems.Thm_ThreeSum_LightScales_root_le_self
import Theorems.Thm_ThreeSum_Scales_microSize_rounding


set_option autoImplicit false
open ThreeSum ThreeSum.LightScales
open Light ThreeSum.Scales
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightScales
theorem _root_.solution (m : ℕ) : microSize m ≤ m :=
  (microSize_rounding m).1.trans (root_le_self m)
end ThreeSum.LightScales
