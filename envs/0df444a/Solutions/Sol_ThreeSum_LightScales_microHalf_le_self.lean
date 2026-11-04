-- Prove2me | solution 1 for ThreeSum.LightScales.microHalf_le_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:29:48.019653+00:00
-- url     : https://prove2.me/submissions/c373dd0a-ec49-4048-9a3b-2f4fda48e4ea

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightScales
import Theorems.Thm_ThreeSum_LightScales_root_le_self

set_option autoImplicit false
open ThreeSum ThreeSum.LightScales
open Light ThreeSum.Scales
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightScales
theorem _root_.solution (m : ℕ) : microHalf m ≤ m :=
  (Nat.div_le_self (Nat.nthRoot 3 m) 2).trans (root_le_self m)
end ThreeSum.LightScales
