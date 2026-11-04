-- Prove2me | solution 1 for ThreeSum.LightOneHot.setupTime_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:26:47.177751+00:00
-- url     : https://prove2.me/submissions/de434f3a-6bac-4c6d-bc13-971098ab6333

import Definitions.Def_Submission_ThreeSum_OneHotMask
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightOneHot

set_option autoImplicit false
open ThreeSum ThreeSum.LightOneHot
open Light ThreeSum.OneHotMask ThreeSum.LightSubsetAddress
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightOneHot
theorem _root_.solution (L : ℕ) : setupTime L ≤ 200*(L+1) := by
  unfold setupTime powTableTime time
  omega
end ThreeSum.LightOneHot
