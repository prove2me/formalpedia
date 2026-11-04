-- Prove2me | solution 1 for ThreeSum.LightSignedLeafTable.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:36:23.327317+00:00
-- url     : https://prove2.me/submissions/ee58f019-e82f-414b-b8bb-fe63a4042b75

import Definitions.Def_Submission_ThreeSum_LightSignedLeafBatch
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightSignedLeafTable

set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedLeafTable
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSignedLeafTable
theorem _root_.solution {W cut : ℕ} (hcut : cut ≤ W) :
    time W cut ≤ 12000*(W+1)^3*(downsetCap W cut+1) := by
  have hp : 1 ≤ (W+1)^2*(downsetCap W cut+1) := by
    have hh : 0 < (W+1)^2*(downsetCap W cut+1) := by positivity
    omega
  have hlin : W+1 ≤ (W+1)^2 := by nlinarith
  have hsmall := Nat.mul_le_mul_right (downsetCap W cut+1) hlin
  have hb : roundBudget W cut+20 ≤ 11000*((W+1)^2*(downsetCap W cut+1)) := by
    unfold roundBudget enumBudget batchBudget
    nlinarith
  have hm := Nat.mul_le_mul_left (cut+1) hb
  have hc := Nat.mul_le_mul_right (11000*((W+1)^2*(downsetCap W cut+1)))
    (Nat.succ_le_succ hcut)
  have hp₃ : 1 ≤ (W+1)^3*(downsetCap W cut+1) := by
    have hh : 0 < (W+1)^3*(downsetCap W cut+1) := by positivity
    omega
  unfold time
  calc
    _ ≤ (W+1)*(11000*((W+1)^2*(downsetCap W cut+1)))+20 :=
      Nat.add_le_add_right (hm.trans hc) 20
    _ = 11000*((W+1)^3*(downsetCap W cut+1))+20 := by ring
    _ ≤ 12000*((W+1)^3*(downsetCap W cut+1)) := by omega
    _ = _ := by ring
end ThreeSum.LightSignedLeafTable
