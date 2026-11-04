-- Prove2me | solution 1 for ThreeSum.LightWeightGather.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:28:21.450174+00:00
-- url     : https://prove2.me/submissions/9bd8f00e-2da7-4827-b31e-f76863d1d127

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightWeightGather

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightGather
open Light
set_option maxHeartbeats 1000000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightWeightGather
theorem _root_.solution (rows width : ℕ) :
    time rows width ≤ 130*(rows+1)*(width+1) := by
  unfold time copyTime
  nlinarith
end ThreeSum.LightWeightGather
