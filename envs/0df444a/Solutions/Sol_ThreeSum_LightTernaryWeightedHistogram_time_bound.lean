-- Prove2me | solution 1 for ThreeSum.LightTernaryWeightedHistogram.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:30:53.05764+00:00
-- url     : https://prove2.me/submissions/0dca45cd-4146-4530-8bcd-0220692a4396

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWeightedHistogram
open Light Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryWeightedHistogram
theorem _root_.solution (n bank : ℕ) : time n bank ≤ 100*(n+bank+1) := by
  unfold time countTime fillTime
  omega
end ThreeSum.LightTernaryWeightedHistogram
