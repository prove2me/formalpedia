-- Prove2me | solution 1 for ThreeSum.LocalParameterBounds.envelope_le_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:48:39.233616+00:00
-- url     : https://prove2.me/submissions/bd030974-a2cc-40b8-ada2-f0e2f6ed3532

import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Theorems.Thm_ThreeSum_Scales_muZero_eq_twice_half


set_option autoImplicit false
open ThreeSum ThreeSum.LocalParameterBounds
open LocalCoverBounds
set_option maxHeartbeats 1000000
namespace ThreeSum.LocalParameterBounds
theorem _root_.solution {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    envelope (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 2000 n := by
  unfold envelope Scales.localSearch
  rw [Scales.muZero_eq_twice_half]
  apply Nat.pow_le_pow_right (by decide)
  nlinarith
end ThreeSum.LocalParameterBounds
