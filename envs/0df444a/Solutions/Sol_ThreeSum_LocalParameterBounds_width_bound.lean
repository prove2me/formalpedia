-- Prove2me | solution 1 for ThreeSum.LocalParameterBounds.width_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:57:37.557254+00:00
-- url     : https://prove2.me/submissions/8a02a501-cdd4-4014-948f-63f57580f50f

import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Theorems.Thm_ThreeSum_LocalParameterBounds_pow_pos

set_option autoImplicit false
open ThreeSum ThreeSum.LocalParameterBounds
open LocalCoverBounds
set_option maxHeartbeats 1000000
namespace ThreeSum.LocalParameterBounds
theorem _root_.solution (h : ℕ) : 512*h+1 ≤ 2^(h+10) := by
  have hh : h < 2^h := Nat.lt_two_pow_self
  have hp := pow_pos h
  rw [pow_add]
  norm_num
  omega
end ThreeSum.LocalParameterBounds
