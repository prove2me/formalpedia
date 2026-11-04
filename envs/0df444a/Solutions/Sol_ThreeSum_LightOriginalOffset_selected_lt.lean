-- Prove2me | solution 1 for ThreeSum.LightOriginalOffset.selected_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:47:22.858208+00:00
-- url     : https://prove2.me/submissions/c260e45c-a1e1-4314-939d-d6b552922d01

import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Definitions.Def_Submission_ThreeSum_LightOriginalOffset
import Theorems.Thm_ThreeSum_LightBalancedOffset_offset_lt


set_option autoImplicit false
open ThreeSum ThreeSum.LightOriginalOffset
open Light LightResidues LightResidueHistogram
open KaratsubaInterface CyclicFold
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
namespace ThreeSum.LightOriginalOffset
theorem _root_.solution (p : ℕ) [NeZero p] (left right : ℕ → ℤ) (nLeft nRight : ℕ) :
    selected p left right nLeft nRight < p := LightBalancedOffset.offset_lt ..
end ThreeSum.LightOriginalOffset
