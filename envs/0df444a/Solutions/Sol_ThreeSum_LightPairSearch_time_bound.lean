-- Prove2me | solution 1 for ThreeSum.LightPairSearch.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:34:39.579671+00:00
-- url     : https://prove2.me/submissions/4245f795-39d8-4cbc-8dda-4e686fcb49c6

import Definitions.Def_Submission_ThreeSum_LightPairSearch
import Definitions.Def_Submission_ThreeSum_LightPairSearchMain

set_option autoImplicit false
open ThreeSum ThreeSum.LightPairSearch
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightPairSearch
theorem _root_.solution (q T : ℕ) (hq : 0<q) : time q T≤q*q*(T+200)+100 := by
  have hsq : q≤q*q := by nlinarith
  unfold time rowTime
  nlinarith
end ThreeSum.LightPairSearch
