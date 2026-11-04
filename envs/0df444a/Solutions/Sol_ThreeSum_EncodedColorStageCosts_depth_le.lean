-- Prove2me | solution 1 for ThreeSum.EncodedColorStageCosts.depth_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:55:32.004065+00:00
-- url     : https://prove2.me/submissions/138f7172-7a23-4d7e-922d-1bed57d87325

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorStageCosts
open Scales BandScales ArithmeticStageBounds
namespace ThreeSum.EncodedColorStageCosts
theorem _root_.solution {n M len len' : ℕ} (hlen : len ≤ len') :
    LightEncodedColorWantedSources.depth n M len ≤ depth n M len' := by
  unfold depth LightEncodedColorWantedSources.depth
  omega
end ThreeSum.EncodedColorStageCosts
