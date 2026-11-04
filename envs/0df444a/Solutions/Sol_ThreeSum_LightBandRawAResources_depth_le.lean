-- Prove2me | solution 1 for ThreeSum.LightBandRawAResources.depth_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:13:27.939208+00:00
-- url     : https://prove2.me/submissions/8f56e00a-82c4-4270-babe-566e3b159ac0

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_LightBandRawAResources
import Theorems.Thm_ThreeSum_LightBandRawAResources_clog_le_self
import Theorems.Thm_ThreeSum_LightBandRawAResources_width_le
import Theorems.Thm_ThreeSum_ColorBandBounds_width_le


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAResources
open Light EncodedColorLayout
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
namespace ThreeSum.LightBandRawAResources
theorem _root_.solution (W n g : ℕ) : LightBandRawAColor.depth W n g ≤ W+5*n+21 := by
  have hc := clog_le_self n
  have hw := width_le n g
  unfold LightBandRawAColor.depth LightColorBands.depth ColorBandBounds.depth
  omega
end ThreeSum.LightBandRawAResources
