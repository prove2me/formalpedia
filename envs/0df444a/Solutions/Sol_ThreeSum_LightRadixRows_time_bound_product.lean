-- Prove2me | solution 1 for ThreeSum.LightRadixRows.time_bound_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:21:23.869907+00:00
-- url     : https://prove2.me/submissions/577a43fc-7728-4709-92ef-9f1098af7db4

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
theorem _root_.solution (m n : ℕ) (hn : 0 < n) : time m n ≤ 130*m*n+20 := by
  unfold time LightReportingAffine.time
  have hmn : m ≤ m*n := Nat.le_mul_of_pos_right m hn
  nlinarith
end ThreeSum.LightRadixRows
