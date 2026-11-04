-- Prove2me | solution 1 for ThreeSum.EncodedColorStageCosts.source_space_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:58:13.402579+00:00
-- url     : https://prove2.me/submissions/caea57ea-a398-4939-99ba-a2999bc12aa9

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorStageCosts
open Scales BandScales ArithmeticStageBounds
namespace ThreeSum.EncodedColorStageCosts
theorem _root_.solution {base bound n p P U D : ℕ} (hb : base ≤ bound) (hp : p ≤ P) :
    SourceFiniteCosts.space base n p U D ≤ SourceFiniteCosts.space bound n P U D := by
  unfold SourceFiniteCosts.space
  gcongr
end ThreeSum.EncodedColorStageCosts
