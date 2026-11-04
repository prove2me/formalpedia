-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.prime_core_space_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:50:08.526324+00:00
-- url     : https://prove2.me/submissions/ef094b43-697d-4d1a-be3e-ebcc979ed5f7

import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeHost
import Definitions.Def_Submission_ThreeSum_EncodedColorPipelineData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Theorems.Thm_ThreeSum_EncodedColorResources_depth_control_bound
import Theorems.Thm_ThreeSum_EncodedColorResources_capacity_bound
import Definitions.Def_WeightedCache3SUM_Alias_aa1db49eeb0333a7
import Theorems.Thm_ThreeSum_EncodedColorResources_scale_bounds


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface
set_option maxHeartbeats 2400000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (free n U : ℕ) :
    LightEncodedColorPrimeCore.space free (maxMod n) (bandSize n) (radix n) (primeWindow n) U ≤
      free+40*scale n+U+10 := by
  have hy := (scale_bounds n).2.2.2.2.2
  have hd := depth_control_bound n
  have hp := (scale_bounds n).2.2.2.2.1
  have hg := (dimensions n).2.2.2.1
  have hc := capacity_bound n
  have hlogy := Nat.log_le_self 2 (4*primeWindow n+1)
  have hlogp := Nat.log_le_self 2 (maxMod n+1)
  have hlogU := Nat.log_le_self 2 (U+1)
  unfold LightEncodedColorPrimeCore.space LightPrimePool.space LightBandPrimeChain.space
    LightWeightedScore.space LightModuloCounts.space EncodedColorPrimeData.prefixBase EncodedColorPrimeData.poolBase
  apply max_le
  · omega
  · apply max_le <;> omega
end ThreeSum.EncodedColorResources
