-- Prove2me | solution 1 for ThreeSum.TernaryColorPreludeResources.depth_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:08:38.997167+00:00
-- url     : https://prove2.me/submissions/b272b744-2bab-4640-8fd9-84477b7ab360

import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryColorPreludeResources_w3sum_ac885d1
import Theorems.Thm_ThreeSum_TernaryColorPreludeResources_one_band_bounds
import Theorems.Thm_ThreeSum_TernaryColorPreludeResources_clog_le_width

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryColorPreludeResources
open Light LightTernaryColorPrelude LightColorParametersCosts StageBounds
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
namespace ThreeSum.TernaryColorPreludeResources
theorem _root_.solution (n : ℕ) : depth n≤ 2*width n+n+18 := by
  obtain ⟨_,_,hw⟩:= one_band_bounds n
  have hc:= clog_le_width n
  unfold depth LightColorBands.depth ColorBandBounds.depth
  omega
end ThreeSum.TernaryColorPreludeResources
