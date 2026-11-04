-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.cover_address_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:23:38.460677+00:00
-- url     : https://prove2.me/submissions/6f0740de-5b34-4d88-a099-b233876be0ec

import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeHost
import Definitions.Def_Submission_ThreeSum_EncodedColorPipelineData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Theorems.Thm_ThreeSum_EncodedColorResources_prime_address_bound
import Theorems.Thm_ThreeSum_EncodedColorResources_depth_control_bound
import Theorems.Thm_ThreeSum_EncodedColorResources_scale_bounds


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface
set_option maxHeartbeats 2400000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (free n : ℕ) :
    EncodedColorPipelineData.coverBase free n ≤ free+2000*(scale n)^3 := by
  have hp := prime_address_bound free n
  have hy := (scale_bounds n).2.2.2.2.2
  have hd := depth_control_bound n
  have hb := (scale_bounds n).1
  unfold EncodedColorPipelineData.coverBase cover EncodedColorPrimeData.nextFree
    EncodedColorPrimeData.prefixBase EncodedColorPrimeData.poolBase
  have hp3 : scale n ≤ (scale n)^3 := Nat.le_self_pow (by decide) _
  nlinarith only [hp,hy,hd,hb,hp3]
end ThreeSum.EncodedColorResources
