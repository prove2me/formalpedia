-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.keyBound_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:41:01.764806+00:00
-- url     : https://prove2.me/submissions/d1a5f3be-754f-4a20-afad-82f6adeb800d

import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Theorems.Thm_ThreeSum_EncodedColorResources_scale_bounds
import Theorems.Thm_ThreeSum_EncodedColorResources_local_bounds
import Theorems.Thm_ThreeSum_EncodedColorResources_radix_power_le

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter
set_option maxHeartbeats 2200000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (n : ℕ) : LightGuardedWanted.keyBound (maxMod n) (half n) (blocks n) ≤ 3*(scale n)^4 := by
  have hP := (scale_bounds n).2.2.2.2.1
  have hL : 512*half n ≤ scale n := by have h := (local_bounds n).width; omega
  have hp : localPrime (half n) ≤ scale n := by have h := (local_bounds n).prime; omega
  have hm := Nat.mul_le_mul (Nat.mul_le_mul hL hp) (radix_power_le n)
  have hs4 : scale n ≤ (scale n)^4 := Nat.le_self_pow (by decide) _
  unfold LightGuardedWanted.keyBound
  nlinarith only [hm,hP,hs4]
end ThreeSum.EncodedColorResources
