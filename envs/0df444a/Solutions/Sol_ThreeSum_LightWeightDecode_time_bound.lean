-- Prove2me | solution 1 for ThreeSum.LightWeightDecode.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:02:13.235269+00:00
-- url     : https://prove2.me/submissions/5bd26ea8-4169-40c3-85c3-1549e831ee39

import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightWeightDecode

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightDecode
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightWeightDecode
theorem _root_.solution (L k : ℕ) : time L k ≤ 600*(L+1)*(k+1) := by
  unfold time LightWeightRow.time LightRadixDigit.time powTableTime
  nlinarith
end ThreeSum.LightWeightDecode
