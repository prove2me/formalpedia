-- Prove2me | solution 1 for ThreeSum.LightBlockSourceHashes.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:43:15.136827+00:00
-- url     : https://prove2.me/submissions/183a6fb9-b38e-402f-be00-f508c3802913

import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_LightMaskHashes
import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceHashes
open Light BlockCoefficientRows
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightBlockSourceHashes
theorem _root_.solution (J L n : ℕ) :
    time J L n ≤ 300*(J+1)*(L+1)+600*(J*L+1)*(n+1)+200 := by
  have hc := LightBlockCoefficients.time_bound J L
  have hh := LightMaskHashes.time_bound (J*L) n
  unfold time
  nlinarith
end ThreeSum.LightBlockSourceHashes
