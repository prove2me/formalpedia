-- Prove2me | solution 1 for ThreeSum.TernaryColorPreludeResources.space_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:08:40.401625+00:00
-- url     : https://prove2.me/submissions/f884294a-82df-4178-b106-c94677192230

import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryColorPreludeResources_w3sum_ac885d1
import Theorems.Thm_ThreeSum_TernaryColorPreludeResources_one_band_bounds

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryColorPreludeResources
open Light LightTernaryColorPrelude LightColorParametersCosts StageBounds
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
namespace ThreeSum.TernaryColorPreludeResources
theorem _root_.solution (free n : ℕ) : space free n≤ free+14*n+width n+16 := by
  obtain ⟨_,hc,hw⟩:= one_band_bounds n
  unfold space LightColorBands.space ColorBandBounds.space work ce cv be bv ae av class2 class1 class0
  omega
end ThreeSum.TernaryColorPreludeResources
