-- Prove2me | solution 1 for ThreeSum.LightTernarySourceHistogram.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:47:19.529034+00:00
-- url     : https://prove2.me/submissions/ba06d01d-35a4-4ab1-9db7-0c8e1524876c

import Definitions.Def_Submission_ThreeSum_LightTernarySourceKeys
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHistogram
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernarySourceKeys_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernarySourceHistogram
open Light ThreeSum.LightArray ThreeSum.LightSubsetAddress
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernarySourceHistogram
theorem _root_.solution (L count bank : ℕ) :
    time L count bank ≤ 1000*(L+1)*(count+bank+1) := by
  have h := LightTernarySourceKeys.time_bound L count
  unfold time LightHistogram.histogramTime LightHistogram.countTime fillTime scaleTime
  nlinarith
end ThreeSum.LightTernarySourceHistogram
