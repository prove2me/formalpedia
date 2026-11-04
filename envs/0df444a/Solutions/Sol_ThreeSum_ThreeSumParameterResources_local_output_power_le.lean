-- Prove2me | solution 1 for ThreeSum.ThreeSumParameterResources.local_output_power_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:00:42.703921+00:00
-- url     : https://prove2.me/submissions/7969755f-c7a3-4556-af6b-623b8fe01a01

import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Definitions.Def_Submission_ThreeSum_ThreeSumParameterResources
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_EncodedColorResources_powers
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr


set_option autoImplicit false
open ThreeSum ThreeSum.ThreeSumParameterResources
open Light Scales BandScales LocalCoverBounds EncodedColorResources StageBounds
set_option maxHeartbeats 2200000
set_option maxRecDepth 14000
namespace ThreeSum.ThreeSumParameterResources
theorem _root_.solution (n : ℕ) :
    LightGlobalSizes.localCount n^(blockCount (inputBits n)) ≤ scale n := by
  have hcount : LightGlobalSizes.localCount n ≤ 2^(512*half n) := Nat.choose_le_two_pow _ _
  calc
    _ ≤ (2^(512*half n))^(blocks n) := Nat.pow_le_pow_left hcount _
    _ = 2^(width n) := by unfold width; rw [← pow_mul]; congr 1; ring
    _ ≤ 2^(width n+1) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ scale n := (powers n).1
end ThreeSum.ThreeSumParameterResources
