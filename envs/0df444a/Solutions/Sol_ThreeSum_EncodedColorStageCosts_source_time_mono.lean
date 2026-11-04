-- Prove2me | solution 1 for ThreeSum.EncodedColorStageCosts.source_time_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:24:08.892229+00:00
-- url     : https://prove2.me/submissions/331ab559-9d13-4325-846d-88eb89f6cbfb

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorStageCosts
open Scales BandScales ArithmeticStageBounds
namespace ThreeSum.EncodedColorStageCosts
theorem _root_.solution {n p P U D : ℕ} (hp : p ≤ P) :
    EncodedColorSourcesCosts.time n p U D ≤ EncodedColorSourcesCosts.time n P U D := by
  unfold EncodedColorSourcesCosts.time SourceFiniteCosts.time
  gcongr
end ThreeSum.EncodedColorStageCosts
