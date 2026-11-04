-- Prove2me | solution 1 for ThreeSum.LightBlockCoefficients.row_end_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:58:08.294505+00:00
-- url     : https://prove2.me/submissions/fce70915-e0b0-47e9-835e-133dd10c497c

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
theorem _root_.solution {J L j : ℕ} (hj : j < J) : j*L+L ≤ J*L := by
  calc
    j*L+L = (j+1)*L := by ring
    _ ≤ J*L := Nat.mul_le_mul_right L (by omega)
end ThreeSum.LightBlockCoefficients
