-- Prove2me | solution 1 for ThreeSum.EncodedColorStageCosts.source_word_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:06:49.128967+00:00
-- url     : https://prove2.me/submissions/de091a73-4dff-4090-98f9-aacf34dc4ee1

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorStageCosts
open Scales BandScales ArithmeticStageBounds
namespace ThreeSum.EncodedColorStageCosts
theorem _root_.solution {n p P U D : ℕ} (hp : p ≤ P) :
    SourceFiniteCosts.word n p U D ≤ SourceFiniteCosts.word n P U D := by
  unfold SourceFiniteCosts.word LightSourceControlsHost.word LightSourceBandHost.word
    LightSourceBandPair.word LightSourceBandStep.word LightSourceResidues.word
  gcongr
end ThreeSum.EncodedColorStageCosts
