-- Prove2me | solution 1 for ThreeSum.LightBandPartition.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:23:56.338483+00:00
-- url     : https://prove2.me/submissions/2a77fb36-d46f-4b8c-89e0-4a5260791433

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSum_LightBandPartition
import Theorems.Thm_ThreeSum_BandPartition_size_le
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPartition
open Light ThreeSum.BandPartition
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandPartition
theorem _root_.solution (n g : ℕ) : time n g ≤ 200*n+200 := by
  have hm := size_le n g
  have hdiv := LightSmallDivide.time_bound (n-1) g
  have hsub : n-1 ≤ n := Nat.sub_le _ _
  unfold time lowerTime upperTime
  omega
end ThreeSum.LightBandPartition
