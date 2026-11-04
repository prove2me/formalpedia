-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.totalKeys_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:03:15.846056+00:00
-- url     : https://prove2.me/submissions/0b19bb30-8b53-4d7d-a3e8-1917375675b3

import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Theorems.Thm_ThreeSum_EncodedColorResources_powers
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter
set_option maxHeartbeats 2200000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (n : ℕ) : LightGuardedWanted.totalKeys (half n) (blocks n) ≤ (scale n)^2 := by
  have hq : outputCount (512*half n) (half n)^(blocks n) ≤ scale n := by
    calc
      _ ≤ (2^(512*half n))^(blocks n) := Nat.pow_le_pow_left (Nat.choose_le_two_pow _ _) _
      _ = 2^(width n) := by unfold width; rw [← pow_mul]; congr 1; ring
      _ ≤ 2^(width n+1) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ scale n := (powers n).1
  unfold LightGuardedWanted.totalKeys LightGlobalKeys.localCount
  rw [mul_pow]
  exact (Nat.mul_le_mul (powers n).2.1 hq).trans_eq (pow_two _).symm
end ThreeSum.EncodedColorResources
