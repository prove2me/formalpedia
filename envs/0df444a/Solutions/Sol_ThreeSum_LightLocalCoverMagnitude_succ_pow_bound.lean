-- Prove2me | solution 1 for ThreeSum.LightLocalCoverMagnitude.succ_pow_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:18:48.276847+00:00
-- url     : https://prove2.me/submissions/8e67ea69-3b54-4bfb-a561-1d610444cf79

import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverMagnitude
open LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverMagnitude
theorem _root_.solution {x e : ℕ} (hx : x ≤ 2^e) : x+1 ≤ 2^(e+1) := by
  have hp := Nat.two_pow_pos e
  rw [pow_succ]
  omega
end ThreeSum.LightLocalCoverMagnitude
