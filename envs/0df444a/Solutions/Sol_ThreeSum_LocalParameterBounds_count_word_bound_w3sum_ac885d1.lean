-- Prove2me | solution 1 for ThreeSum.LocalParameterBounds.count_word_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:04:45.586571+00:00
-- url     : https://prove2.me/submissions/6a2f7e21-a163-40db-a028-5252952bbaba

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
theorem _root_.solution (h : ℕ) : LightLocalCounts.word h ≤ 2^(1024*h+11) := by
  have ha : (1024 : ℕ) ≤ 2^(1024*h+10) := by
    exact (by decide : 1024 ≤ 2^10).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hb : 4*(2^(512*h+1))^2 = 2^(1024*h+4) := by
    change 2^2*(2^(512*h+1))^2 = _
    rw [← pow_mul,← pow_add]
    congr 1 <;> omega
  have hc : 2^(1024*h+4) ≤ 2^(1024*h+10) := Nat.pow_le_pow_right (by decide) (by omega)
  have hd : 2^(1024*h+11) = 2*2^(1024*h+10) := by
    rw [show 1024*h+11 = (1024*h+10)+1 by omega,pow_succ]
    omega
  unfold LightLocalCounts.word
  rw [hb,hd]
  omega
end ThreeSum.LocalParameterBounds
