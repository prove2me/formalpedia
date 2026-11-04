-- Prove2me | solution 1 for ThreeSum.LocalParameterBounds.selected_word_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:04:47.209094+00:00
-- url     : https://prove2.me/submissions/7c404fae-9f84-4909-88a0-d565ba5bfeb8

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
theorem _root_.solution (h : ℕ) :
    LightSelectedPrime.word (localThreshold h) ≤ 2^(514*h+8) := by
  have ht := threshold_bound h
  have hx := pow_pos (514*h)
  unfold LightSelectedPrime.word
  rw [pow_add]
  norm_num
  omega
end ThreeSum.LocalParameterBounds
