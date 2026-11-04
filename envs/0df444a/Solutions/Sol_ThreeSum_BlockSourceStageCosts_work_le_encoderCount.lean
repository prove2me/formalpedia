-- Prove2me | solution 1 for ThreeSum.BlockSourceStageCosts.work_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:57:56.951313+00:00
-- url     : https://prove2.me/submissions/8b9c3311-13b8-4d88-b73f-fcf70b7c0efe

import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedProgram
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Definitions.Def_Submission_ThreeSum_BlockSourceStageCosts
import Theorems.Thm_ThreeSum_BlockSourceSharing_downset_add_one_le_fullOutputs
import Theorems.Thm_ThreeSum_BlockSourceSharing_width_eq
import Definitions.Def_WeightedCache3SUM_Alias_b52a695b828f0da1


set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceStageCosts
open Scales TrimScales StageBounds CostLedger BlockSourceSharing
namespace ThreeSum.BlockSourceStageCosts
theorem _root_.solution (n : ℕ) :
    work n ≤ LightBlockSourceRetainedProgram.factor
      (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)*encoderCount n := by
  have hcut : mu n ≤ blockCount (inputBits n)*(512*microHalf (inputBits n)) := by
    rw [width_eq]
    omega
  have ht := LightBlockSourceRetainedProgram.time_le_factor hcut
  rw [width_eq] at ht
  have hd := downset_add_one_le_fullOutputs n
  have he : bandCount n*scheduleCount n*fullOutputs n ≤ encoderCount n := by
    calc
      _ ≤ 2*(bandCount n*scheduleCount n*fullOutputs n) :=
        Nat.le_mul_of_pos_left _ (by omega)
      _ = encoderCount n := by unfold encoderCount; ring
  unfold work
  calc
    _ ≤ bandCount n*scheduleCount n*
        (LightBlockSourceRetainedProgram.factor (microHalf (inputBits n))
          (blockCount (inputBits n))*((256*mu n+2)*fullOutputs n)) :=
      Nat.mul_le_mul_left _ (ht.trans (Nat.mul_le_mul_left _ hd))
    _ = LightBlockSourceRetainedProgram.factor (microHalf (inputBits n))
        (blockCount (inputBits n))*(256*mu n+2)*(bandCount n*scheduleCount n*fullOutputs n) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ he
end ThreeSum.BlockSourceStageCosts
