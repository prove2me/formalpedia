-- Prove2me | solution 1 for ThreeSum.LocalParameterBounds.time_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:10:30.895486+00:00
-- url     : https://prove2.me/submissions/3b1dda38-2edf-4d8a-83f4-9cf2733b0748

import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Theorems.Thm_ThreeSum_LocalParameterBounds_count_time_bound
import Theorems.Thm_ThreeSum_LocalParameterBounds_selected_time_bound
import Theorems.Thm_ThreeSum_LocalParameterBounds_cap_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LocalParameterBounds
open LocalCoverBounds
set_option maxHeartbeats 1000000
namespace ThreeSum.LocalParameterBounds
theorem _root_.solution (h : ℕ) : LightLocalParameters.time h ≤ envelope h := by
  have hc : LightLocalCounts.time h ≤ base h :=
    (count_time_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hp : LightSelectedPrime.time (localThreshold h) ≤ base h :=
    (selected_time_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hd : LightSmallDivide.time (LightLocalParameters.numerator h) (localPrime h) ≤ base h :=
    (cap_time_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hk : 200 ≤ base h := (by decide : 200 ≤ 2^8).trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  have he : envelope h = 4*base h := by unfold envelope base; rw [pow_add]; norm_num; omega
  unfold LightLocalParameters.time
  rw [he]
  omega
end ThreeSum.LocalParameterBounds
