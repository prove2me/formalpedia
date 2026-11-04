-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.schedule_power_le_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:16:12.41989+00:00
-- url     : https://prove2.me/submissions/6f1bafc1-2074-49af-b938-b12e21c456a5

import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Theorems.Thm_ThreeSum_EncodedColorResources_local_bounds
import Theorems.Thm_ThreeSum_EncodedColorResources_powers

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter
set_option maxHeartbeats 2200000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (n : ℕ) : (scheduleSize (half n)+1)^(blocks n+1) ≤ 2*(scale n)^3 := by
  have hS : 1 ≤ scheduleSize (half n) := by change 0 < scheduleSize (half n); unfold scheduleSize LocalHashMoments.scheduleLength; positivity
  have hrow : scheduleSize (half n) ≤ scale n := by have h := (local_bounds n).rounds; omega
  have hocc : scheduleSize (half n)^(blocks n) ≤ scale n := (powers n).2.1
  calc
    _ ≤ (2*scheduleSize (half n))^(blocks n+1) := Nat.pow_le_pow_left (by omega) _
    _ = 2*(2^(blocks n)*scheduleSize (half n)^(blocks n)*scheduleSize (half n)) := by
      rw [mul_pow,pow_succ,pow_succ]
      ring
    _ ≤ 2*(scale n*scale n*scale n) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.mul_le_mul (powers n).2.2.2 hocc) hrow)
    _ = _ := by ring
end ThreeSum.EncodedColorResources
