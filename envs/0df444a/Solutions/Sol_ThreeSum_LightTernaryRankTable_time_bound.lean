-- Prove2me | solution 1 for ThreeSum.LightTernaryRankTable.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:47:45.015283+00:00
-- url     : https://prove2.me/submissions/22bf7678-b636-4c73-8e9b-533543ef19dd

import Definitions.Def_Submission_ThreeSum_LightTernaryRank
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRankTable
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType
  ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryRankTable
theorem _root_.solution (N n : ℕ) : time N n ≤ 2000*(N+1)^2*(n+1) := by
  unfold time LightTernaryRank.time LightTernaryCodes.digitTime LightMaskErase.time
  nlinarith
end ThreeSum.LightTernaryRankTable
