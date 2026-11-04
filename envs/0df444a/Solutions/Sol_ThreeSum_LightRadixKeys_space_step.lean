-- Prove2me | solution 1 for ThreeSum.LightRadixKeys.space_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:22:07.024719+00:00
-- url     : https://prove2.me/submissions/8fb41d90-f082-43c5-a4b9-6c24650e6f09

import Definitions.Def_Submission_ThreeSum_LightRadixRows
import Definitions.Def_Submission_ThreeSum_LightRadixKeys

set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixKeys
open Light RadixKeyLists
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
namespace ThreeSum.LightRadixKeys
theorem _root_.solution (dst m j : ℕ) : space dst m j ≤ space dst m (j+1) := by
  unfold space
  rw [offset]
  omega
end ThreeSum.LightRadixKeys
