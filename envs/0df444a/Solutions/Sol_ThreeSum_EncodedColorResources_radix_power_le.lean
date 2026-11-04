-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.radix_power_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:21:58.778417+00:00
-- url     : https://prove2.me/submissions/e0dd3e3a-f288-4fbd-ae51-b702b46472c4

import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Theorems.Thm_ThreeSum_EncodedColorResources_powers
import Theorems.Thm_ThreeSum_EncodedColorResources_modulus_le
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter
set_option maxHeartbeats 2200000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (n : ℕ) : (localPrime (half n)+1)^(blocks n) ≤ (scale n)^2 := by
  have hp := localPrime_pos (half n)
  have hmod := modulus_le n
  calc
    _ ≤ (2*localPrime (half n))^(blocks n) := Nat.pow_le_pow_left (by omega) _
    _ = 2^(blocks n)*localPrime (half n)^(blocks n) := mul_pow _ _ _
    _ ≤ scale n*scale n := Nat.mul_le_mul (powers n).2.2.2 hmod
    _ = _ := by ring
end ThreeSum.EncodedColorResources
