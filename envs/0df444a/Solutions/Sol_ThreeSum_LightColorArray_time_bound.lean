-- Prove2me | solution 1 for ThreeSum.LightColorArray.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:43:24.171044+00:00
-- url     : https://prove2.me/submissions/d3ca9b47-8554-4148-bf88-fb3967462e1c

import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightColorArray

set_option autoImplicit false
open ThreeSum ThreeSum.LightColorArray
open Light LightSubsetAddress
set_option maxHeartbeats 1200000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightColorArray
theorem _root_.solution (W n : ℕ) : time W n ≤ 600*(W+1)*(n+1) := by
  unfold time powTableTime LightColorIndex.time LightMaskErase.time
  nlinarith
end ThreeSum.LightColorArray
