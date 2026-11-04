-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.prime_depth_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:52:19.657009+00:00
-- url     : https://prove2.me/submissions/3326bec4-5da9-4f66-9d10-1eb78db33dd0

import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeHost
import Definitions.Def_Submission_ThreeSum_EncodedColorPipelineData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Theorems.Thm_ThreeSum_ColorBandBounds_depth_le
import Theorems.Thm_ThreeSum_EncodedColorResources_scale_bounds
import Theorems.Thm_ThreeSum_EncodedColorStageCosts_depth_le
import Theorems.Thm_ThreeSum_LightBandRawAResources_clog_le_self
import Theorems.Thm_ThreeSum_LightBandRawAResources_depth_le
import Theorems.Thm_ThreeSum_LightScales_inputBits_le_self


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface
set_option maxHeartbeats 2400000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (n : ℕ) : LightEncodedColorPrimeHost.depth n ≤ 10*scale n := by
  have hb := (scale_bounds n).1
  have hn := (scale_bounds n).2.1
  have hW := (Nat.add_le_add_right (LightScales.inputBits_le_self n) 1).trans hn
  have hp := (scale_bounds n).2.2.2.2.1
  have hraw := LightBandRawAResources.depth_le (inputBits n+1) n (bandSize n)
  have hc := (LightBandRawAResources.clog_le_self (maxMod n)).trans hp
  unfold LightEncodedColorPrimeHost.depth
  apply max_le <;> omega
end ThreeSum.EncodedColorResources
