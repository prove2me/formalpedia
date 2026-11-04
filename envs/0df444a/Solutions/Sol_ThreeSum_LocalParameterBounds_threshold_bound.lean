-- Prove2me | solution 1 for ThreeSum.LocalParameterBounds.threshold_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:57:36.396336+00:00
-- url     : https://prove2.me/submissions/19b6bfdf-3fd5-49e5-9aa6-0492ae2fb956

import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr


set_option autoImplicit false
open ThreeSum ThreeSum.LocalParameterBounds
open LocalCoverBounds
set_option maxHeartbeats 1000000
namespace ThreeSum.LocalParameterBounds
theorem _root_.solution (h : ℕ) : localThreshold h ≤ 2^(514*h) := by
  calc
    localThreshold h ≤ 2^(512*h)*2^(2*h) :=
      Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _)
    _ = 2^(514*h) := by rw [← pow_add]; congr 1 <;> omega
end ThreeSum.LocalParameterBounds
