-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixTable.time_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:09:32.442577+00:00
-- url     : https://prove2.me/submissions/219eb31c-68ee-483e-9b77-87b33e994247

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBatch
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixTable

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixTable
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostSuffix
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightReportingSuffixTable
theorem _root_.solution {W V cut : ℕ} (hV : V ≤ W) (hcut : cut ≤ V) :
    time W V cut ≤ 12000*(W+1)^3*(downsetCap V cut+1) := by
  have hp : 1 ≤ (W+1)^2*(downsetCap V cut+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hlin : V+1 ≤ (W+1)^2 := by nlinarith
  have hsmall := Nat.mul_le_mul_right (downsetCap V cut+1) hlin
  have hb : roundBudget W V cut+20 ≤ 11000*((W+1)^2*(downsetCap V cut+1)) := by
    unfold roundBudget enumBudget batchBudget
    nlinarith
  have hm := Nat.mul_le_mul_left (cut+1) hb
  have hc := Nat.mul_le_mul_right (11000*((W+1)^2*(downsetCap V cut+1)))
    (Nat.succ_le_succ (hcut.trans hV))
  have hp₃ : 1 ≤ (W+1)^3*(downsetCap V cut+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold time
  calc
    _ ≤ (W+1)*(11000*((W+1)^2*(downsetCap V cut+1)))+20 :=
      Nat.add_le_add_right (hm.trans hc) 20
    _ = 11000*((W+1)^3*(downsetCap V cut+1))+20 := by ring
    _ ≤ 12000*((W+1)^3*(downsetCap V cut+1)) := by omega
    _ = _ := by ring
end ThreeSum.LightReportingSuffixTable
