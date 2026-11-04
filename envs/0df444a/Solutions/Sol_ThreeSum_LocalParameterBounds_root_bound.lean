-- Prove2me | solution 1 for ThreeSum.LocalParameterBounds.root_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:09:01.414806+00:00
-- url     : https://prove2.me/submissions/162c7c64-56d8-46ef-a859-b753135c23c0

import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Theorems.Thm_ThreeSum_LocalParameterBounds_pow_pos
import Theorems.Thm_ThreeSum_LocalParameterBounds_threshold_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LocalParameterBounds
open LocalCoverBounds
set_option maxHeartbeats 1000000
namespace ThreeSum.LocalParameterBounds
theorem _root_.solution (h : ℕ) : rootCeiling (localThreshold h) ≤ 2*2^(514*h) := by
  have hs := Nat.sqrt_le_self (localThreshold h-1)
  have ht := threshold_bound h
  have hp := pow_pos (514*h)
  unfold rootCeiling
  omega
end ThreeSum.LocalParameterBounds
