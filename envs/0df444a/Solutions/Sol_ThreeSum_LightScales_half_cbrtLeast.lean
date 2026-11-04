-- Prove2me | solution 1 for ThreeSum.LightScales.half_cbrtLeast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:42:54.854989+00:00
-- url     : https://prove2.me/submissions/5d4f89f9-2b55-41c6-ba10-a3e1e2a46463

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightScales
import Theorems.Thm_ThreeSum_LightScales_cbrtLeast_successor

set_option autoImplicit false
open ThreeSum ThreeSum.LightScales
open Light ThreeSum.Scales
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightScales
theorem _root_.solution (m : ℕ) : (cbrtLeast (m+1)+1)/2 = microHalf m+1 := by
  rw [cbrtLeast_successor]
  unfold microHalf
  omega
end ThreeSum.LightScales
