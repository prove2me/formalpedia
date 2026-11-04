-- Prove2me | solution 1 for ThreeSum.LightReportingGatherPair.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:37:37.692219+00:00
-- url     : https://prove2.me/submissions/382e408b-5bcb-4445-bb47-734d6d3cb99a

import Definitions.Def_Submission_ThreeSum_LightReportingGather
import Definitions.Def_Submission_ThreeSum_LightReportingGatherPair

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingGatherPair
open Light
variable {lim : Limits}
namespace ThreeSum.LightReportingGatherPair
theorem _root_.solution (t : ℕ) : time t ≤ 80*t+80 := by
  unfold time LightReportingGather.time
  omega
end ThreeSum.LightReportingGatherPair
