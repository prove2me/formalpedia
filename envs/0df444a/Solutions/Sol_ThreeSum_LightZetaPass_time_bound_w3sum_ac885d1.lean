-- Prove2me | solution 1 for ThreeSum.LightZetaPass.time_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:35:44.416189+00:00
-- url     : https://prove2.me/submissions/0c74c48b-6b19-4924-9535-920dbbade38f

import Definitions.Def_Submission_ThreeSum_LightZetaBatch
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightZetaPass

set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaPass
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightZetaPass
theorem _root_.solution {L cut : ℕ} (hcut : cut ≤ L) :
    time L cut ≤ 4000*(L+1)^3*(downsetCap L cut+1) := by
  have hp : 1 ≤ (L+1)^2*(downsetCap L cut+1) := by
    have hh : 0 < (L+1)^2*(downsetCap L cut+1) := by positivity
    omega
  have hlin : L+1 ≤ (L+1)^2 := by nlinarith
  have hsmall := Nat.mul_le_mul_right (downsetCap L cut+1) hlin
  have hb : roundBudget L cut+20 ≤ 3000*((L+1)^2*(downsetCap L cut+1)) := by
    unfold roundBudget enumBudget batchBudget
    nlinarith
  have hm := Nat.mul_le_mul_left (cut+1) hb
  have hc := Nat.mul_le_mul_right (3000*((L+1)^2*(downsetCap L cut+1)))
    (Nat.succ_le_succ hcut)
  have hp₃ : 1 ≤ (L+1)^3*(downsetCap L cut+1) := by
    have hh : 0 < (L+1)^3*(downsetCap L cut+1) := by positivity
    omega
  unfold time
  calc
    _ ≤ (L+1)*(3000*((L+1)^2*(downsetCap L cut+1)))+20 :=
      Nat.add_le_add_right (hm.trans hc) 20
    _ = 3000*((L+1)^3*(downsetCap L cut+1))+20 := by ring
    _ ≤ 4000*((L+1)^3*(downsetCap L cut+1)) := by omega
    _ = _ := by ring
end ThreeSum.LightZetaPass
