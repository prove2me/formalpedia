-- Prove2me | solution 1 for ThreeSum.LightSourceOccurrenceArray.time_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:57:48.757847+00:00
-- url     : https://prove2.me/submissions/97d1f4c6-56c3-49af-8f31-0794ab1d71b7

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_LightSourceOccurrenceArray

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceOccurrenceArray
open Light OutputDecodeOrder
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceOccurrenceArray
theorem _root_.solution (N J : ℕ) :
    time N J ≤ 300*(N+1)*(J+1)*(Nat.log 2 (N+1)+2) := by
  have hlog : 2 ≤ Nat.log 2 (N+1)+2 := by omega
  have hinner : J*(100*(Nat.log 2 (N+1)+2)+100)+30+150 ≤
      300*(J+1)*(Nat.log 2 (N+1)+2) := by
    have hscale := Nat.mul_le_mul_left J hlog
    nlinarith
  have hc : 10 ≤ 300*(J+1)*(Nat.log 2 (N+1)+2) := by nlinarith
  unfold time LightOutputDecodeDigits.time LightOutputDecodeDivide.budget
  calc
    _ ≤ N*(300*(J+1)*(Nat.log 2 (N+1)+2))+10 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left N hinner) 10
    _ ≤ (N+1)*(300*(J+1)*(Nat.log 2 (N+1)+2)) := by nlinarith
    _ = _ := by ring
end ThreeSum.LightSourceOccurrenceArray
