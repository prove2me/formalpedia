-- Prove2me | solution 1 for ThreeSum.LocalParameterBounds.word_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:19:44.522197+00:00
-- url     : https://prove2.me/submissions/b344b01f-2c30-4928-9c9c-1c28f986bb0e

import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Definitions.Def_WeightedCache3SUM_Alias_343e7d8052289a7d
import Theorems.Thm_ThreeSum_LocalParameterBounds_selected_word_bound
import Theorems.Thm_ThreeSum_LocalParameterBounds_cap_word_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LocalParameterBounds
open LocalCoverBounds
set_option maxHeartbeats 1000000
namespace ThreeSum.LocalParameterBounds
theorem _root_.solution (h : ℕ) : LightLocalParameters.word h ≤ envelope h := by
  have hc : LightLocalCounts.word h ≤ base h :=
    (count_word_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hp : LightSelectedPrime.word (localThreshold h) ≤ base h :=
    (selected_word_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hd : 20*(localPrime h+vertexCount (512*h) h+1) ≤ base h :=
    (cap_word_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have he : envelope h = 4*base h := by unfold envelope base; rw [pow_add]; norm_num; omega
  unfold LightLocalParameters.word
  rw [he]
  omega
end ThreeSum.LocalParameterBounds
