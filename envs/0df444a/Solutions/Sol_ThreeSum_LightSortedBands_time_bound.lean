-- Prove2me | solution 1 for ThreeSum.LightSortedBands.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:44:36.813358+00:00
-- url     : https://prove2.me/submissions/65771308-1210-4449-b9ee-dd51b6c24cce

import Definitions.Def_Submission_ThreeSum_LightNormalize
import Definitions.Def_Submission_ThreeSum_LightBandPartition
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Theorems.Thm_ThreeSum_LightBandEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightBandPartition_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightNormalize_time_bound
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightSortedBands
open Light ThreeSum.BandPartition
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSortedBands
theorem _root_.solution (n : ℕ) : time n ≤ 700*(n+1)*(Nat.clog 2 n+1) := by
  have h := LightNormalize.time_bound n
  unfold time
  nlinarith [Nat.zero_le (n*Nat.clog 2 n)]
end ThreeSum.LightSortedBands
