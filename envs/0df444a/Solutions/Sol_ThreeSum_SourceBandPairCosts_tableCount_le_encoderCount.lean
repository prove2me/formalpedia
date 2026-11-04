-- Prove2me | solution 1 for ThreeSum.SourceBandPairCosts.tableCount_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:17:29.444753+00:00
-- url     : https://prove2.me/submissions/7da1b88d-f5f0-4869-8b6a-0c7574a06210

import Definitions.Def_Submission_ThreeSum_LightSourceBandPair
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Theorems.Thm_ThreeSum_CostLedger_bandCount_mul_bounds


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairCosts
open Scales TrimScales StageBounds CostLedger BandScales SourceBandPairData
namespace ThreeSum.SourceBandPairCosts
theorem _root_.solution {n : ℕ} (hn : 0 < n) : tableCount n ≤ encoderCount n := by
  have hb : 0 < bandCount n := by
    have hp := (bandCount_mul_bounds n).1
    by_contra h
    have hz : bandCount n=0 := by omega
    rw [hz,Nat.mul_zero] at hp
    omega
  calc
    _ ≤ bandCount n*tableCount n := Nat.le_mul_of_pos_left _ hb
    _ ≤ 2*(bandCount n*tableCount n) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold tableCount encoderCount; ring
end ThreeSum.SourceBandPairCosts
