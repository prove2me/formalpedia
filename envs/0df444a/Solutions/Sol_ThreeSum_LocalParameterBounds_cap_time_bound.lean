-- Prove2me | solution 1 for ThreeSum.LocalParameterBounds.cap_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:04:44.485356+00:00
-- url     : https://prove2.me/submissions/91154096-a400-44c7-8398-dd8995df2858

import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Theorems.Thm_ThreeSum_LocalParameterBounds_pow_pos
import Theorems.Thm_ThreeSum_LocalParameterBounds_vertex_bound
import Theorems.Thm_ThreeSum_LocalParameterBounds_prime_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LocalParameterBounds
open LocalCoverBounds
set_option maxHeartbeats 1000000
namespace ThreeSum.LocalParameterBounds
theorem _root_.solution (h : ℕ) :
    LightSmallDivide.time (LightLocalParameters.numerator h) (localPrime h) ≤ 2^(514*h+10) := by
  have hp := prime_bound h
  have hv := vertex_bound h
  have hx := pow_pos (514*h)
  rw [pow_add] at hp
  norm_num at hp
  have hn : LightLocalParameters.numerator h ≤ 24*2^(514*h) := by
    unfold LightLocalParameters.numerator
    omega
  have hq := Nat.div_le_self (LightLocalParameters.numerator h) (localPrime h)
  unfold LightSmallDivide.time
  rw [pow_add]
  norm_num
  omega
end ThreeSum.LocalParameterBounds
