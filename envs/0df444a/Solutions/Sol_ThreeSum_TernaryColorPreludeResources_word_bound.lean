-- Prove2me | solution 1 for ThreeSum.TernaryColorPreludeResources.word_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:08:37.771856+00:00
-- url     : https://prove2.me/submissions/820ae94d-ff75-43a0-b532-6b5dc5744c0f

import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryColorPreludeResources_w3sum_ac885d1
import Theorems.Thm_ThreeSum_TernaryColorPreludeResources_one_band_bounds
import Theorems.Thm_ThreeSum_TernaryColorPreludeResources_width_le
import Theorems.Thm_ThreeSum_TernaryColorPreludeResources_code_power_bound
import Theorems.Thm_ThreeSum_ColorBandBounds_width_le


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryColorPreludeResources
open Light LightTernaryColorPrelude LightColorParametersCosts StageBounds
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
namespace ThreeSum.TernaryColorPreludeResources
theorem _root_.solution (n U : ℕ) : word n U≤ 1000*(n+1)*(U+1) := by
  obtain ⟨hs,_,_⟩:= one_band_bounds n
  have hp:= code_power_bound n
  have hw:= width_le n
  unfold word LightColorBands.word ColorBandBounds.word LightBandEnumeration.word
  nlinarith only [hs,hp,hw,Nat.zero_le (n*U)]
end ThreeSum.TernaryColorPreludeResources
