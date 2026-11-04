-- Prove2me | solution 1 for ThreeSum.LightRadixRows.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:31:32.331682+00:00
-- url     : https://prove2.me/submissions/593e8127-1b11-4258-87b0-43c599b5fb05

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightRadixRows

set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixRows
open Light RadixKeyLists
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightRadixRows
theorem _root_.solution (m n : ℕ) : time m n ≤ 130*(m+1)*(n+1) := by
  unfold time LightReportingAffine.time
  nlinarith
end ThreeSum.LightRadixRows
