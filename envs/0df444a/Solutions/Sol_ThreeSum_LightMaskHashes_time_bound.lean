-- Prove2me | solution 1 for ThreeSum.LightMaskHashes.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:36:25.095406+00:00
-- url     : https://prove2.me/submissions/bb74ee55-6202-4e9e-a48a-5b1f524a7511

import Definitions.Def_Submission_ThreeSum_LightOneHot
import Definitions.Def_Submission_ThreeSum_LightMaskHashes

set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskHashes
open Light LightSubsetAddress
set_option maxHeartbeats 1000000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightMaskHashes
theorem _root_.solution (L n : ℕ) : time L n ≤ 300*(L+1)*(n+1) := by
  unfold time powTableTime LightOneHot.time
  nlinarith
end ThreeSum.LightMaskHashes
