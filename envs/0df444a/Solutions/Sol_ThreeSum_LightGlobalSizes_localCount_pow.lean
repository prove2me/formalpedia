-- Prove2me | solution 1 for ThreeSum.LightGlobalSizes.localCount_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:40:35.563248+00:00
-- url     : https://prove2.me/submissions/5d2c65cf-4d91-48d5-a551-d3d0112f2c0b

import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_BandScales
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightGlobalSizes
import Theorems.Thm_ThreeSum_Scales_muZero_eq_twice_half


set_option autoImplicit false
open ThreeSum ThreeSum.LightGlobalSizes
set_option maxHeartbeats 1000000
open Light LocalCoverBounds
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightGlobalSizes
theorem _root_.solution (n : ℕ) :
    localCount n ^ Scales.blockCount (Scales.inputBits n) = Scales.typedOutputs n := by
  have hwidth : 256*Scales.muZero n = 512*Scales.microHalf (Scales.inputBits n) := by
    rw [Scales.muZero_eq_twice_half]
    ring
  unfold Scales.typedOutputs
  rw [hwidth,Scales.muZero_eq_twice_half]
  rfl
end ThreeSum.LightGlobalSizes
