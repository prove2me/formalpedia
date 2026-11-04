-- Prove2me | solution 1 for ThreeSum.LightLocalCoverCost.matrix_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:24:23.630206+00:00
-- url     : https://prove2.me/submissions/69abc58c-f621-42de-b52d-dfc20ad8f673

import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Theorems.Thm_ThreeSum_LightLocalCoverCost_candidate_time_bound
import Theorems.Thm_ThreeSum_LocalParameterBounds_pow_pos


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverCost
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout
set_option maxHeartbeats 1500000
namespace ThreeSum.LightLocalCoverCost
theorem _root_.solution {L n p N B : ℕ}
    (hB : 1 ≤ B) (hL : L+1 ≤ B) (hn : n+1 ≤ B) (hp : p+1 ≤ B) (hN : N+1 ≤ B) :
    LightLocalCoverMatrix.time L n p N ≤ 6000*B^5 := by
  have hc := candidate_time_bound hB hL hn hp hN
  have hm := Nat.mul_le_mul (show N ≤ B by omega) (Nat.add_le_add_right hc 200)
  have hb5 : B ≤ B^5 := Nat.le_self_pow (by decide) B
  have hb5' : 1 ≤ B^5 := Nat.pow_pos (by omega)
  unfold LightLocalCoverMatrix.time
  ring_nf at hm ⊢
  omega
end ThreeSum.LightLocalCoverCost
