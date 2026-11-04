-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.capacity_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:19:15.525655+00:00
-- url     : https://prove2.me/submissions/15339195-ae55-4203-93bf-e432c2ea9a63

import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeHost
import Definitions.Def_Submission_ThreeSum_EncodedColorPipelineData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Theorems.Thm_ThreeSum_ArithmeticStageBounds_maxMod_pos
import Theorems.Thm_ThreeSum_EncodedColorResources_scale_bounds
import Definitions.Def_WeightedCache3SUM_Alias_44fe933b0cad9ef5


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface
set_option maxHeartbeats 2400000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (n : ℕ) : capacity (maxMod n) ≤ 2*scale n :=
  (capacity_lt_twice (maxMod_pos n)).le.trans (Nat.mul_le_mul_left 2 (scale_bounds n).2.2.2.2.1)
end ThreeSum.EncodedColorResources
