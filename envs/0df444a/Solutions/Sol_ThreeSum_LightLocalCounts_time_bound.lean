-- Prove2me | solution 1 for ThreeSum.LightLocalCounts.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:39:23.629824+00:00
-- url     : https://prove2.me/submissions/f532971c-42a9-4a71-b195-0f4eae71b324

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCounts
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCounts
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open Light LocalCoverBounds LightPascal LightSubsetAddress
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightLocalCounts
theorem _root_.solution (h : ℕ) : time h ≤ 1700*(512*h+1)^2 := by
  have ht := LightSubsetSetup.time_bound (512*h)
  have hs : 0 < (512*h+1)^2 := Nat.pow_pos (by omega)
  unfold time
  nlinarith
end ThreeSum.LightLocalCounts
