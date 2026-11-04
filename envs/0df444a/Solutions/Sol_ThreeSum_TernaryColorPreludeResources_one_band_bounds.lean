-- Prove2me | solution 1 for ThreeSum.TernaryColorPreludeResources.one_band_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:01:57.561503+00:00
-- url     : https://prove2.me/submissions/3a17003b-8077-4be4-b7eb-7279b1dcc735

import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryColorPreludeResources_w3sum_ac885d1
import Theorems.Thm_ThreeSum_LightTernaryColorPrelude_one_band


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryColorPreludeResources
open Light LightTernaryColorPrelude LightColorParametersCosts StageBounds
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
namespace ThreeSum.TernaryColorPreludeResources
theorem _root_.solution (n : ℕ) :
    BandPartition.size n n≤ 1 ∧ ColorBandBounds.count n n≤ 3 ∧ ColorBandBounds.width n n≤ 2 := by
  by_cases hn : n=0
  · subst n
    norm_num [BandPartition.size,ColorBandBounds.count,ColorBandBounds.width,LightBandEnumeration.width]
  · obtain ⟨h,h',h''⟩:= one_band (by omega : 0<n)
    exact ⟨h.le,h'.le,h''.le⟩
end ThreeSum.TernaryColorPreludeResources
