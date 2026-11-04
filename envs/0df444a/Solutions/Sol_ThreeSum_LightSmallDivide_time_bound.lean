-- Prove2me | solution 1 for ThreeSum.LightSmallDivide.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:39:28.590557+00:00
-- url     : https://prove2.me/submissions/6a60aab5-62ff-4e84-abea-c4f051e5ee0e

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSmallDivide

set_option autoImplicit false
open ThreeSum ThreeSum.LightSmallDivide
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSmallDivide
theorem _root_.solution (a b : ℕ) : time a b ≤ 20*a+40 := by
  have h := Nat.div_le_self a b
  unfold time
  omega
end ThreeSum.LightSmallDivide
