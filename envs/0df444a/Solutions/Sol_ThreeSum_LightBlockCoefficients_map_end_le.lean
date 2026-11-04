-- Prove2me | solution 1 for ThreeSum.LightBlockCoefficients.map_end_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:20:34.632217+00:00
-- url     : https://prove2.me/submissions/48f5f401-966d-4862-9766-1ad8e60094ce

import Definitions.Def_Submission_ThreeSum_LightScaleArray
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_BlockIndex
import Definitions.Def_Submission_ThreeSum_LightBlockCoefficients

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockCoefficients
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBlockCoefficients
theorem _root_.solution {M L s : ℕ} (hs : s < M) : 2*L*s+L+L ≤ 2*L*M := by
  calc
    2*L*s+L+L = 2*L*(s+1) := by ring
    _ ≤ 2*L*M := Nat.mul_le_mul_left (2*L) (by omega)
end ThreeSum.LightBlockCoefficients
