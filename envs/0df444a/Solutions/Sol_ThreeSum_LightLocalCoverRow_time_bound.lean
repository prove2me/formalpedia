-- Prove2me | solution 1 for ThreeSum.LightLocalCoverRow.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:40:46.691364+00:00
-- url     : https://prove2.me/submissions/3acc87f7-5bb1-4fa5-90be-81ed3364ae35

import Definitions.Def_Submission_ThreeSum_LightPairFlags
import Definitions.Def_Submission_ThreeSum_LightSupportMark
import Definitions.Def_Submission_ThreeSum_LightLocalCoverRow
import Theorems.Thm_ThreeSum_LightPairFlags_time_bound
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverRow
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightLocalCoverRow
theorem _root_.solution (L n p : ℕ) : time L n p ≤ 600*(n*n+1)*(L+n+p*p+1) := by
  have ht := LightPairFlags.time_bound L n
  unfold time LightSupportMark.time LightSupportMark.markTime fillTime
  nlinarith
end ThreeSum.LightLocalCoverRow
