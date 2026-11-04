-- Prove2me | solution 1 for ThreeSum.ColorBandBounds.width_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:58:32.611227+00:00
-- url     : https://prove2.me/submissions/f197b6ae-679b-469b-800a-53dca2675626

import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
import Definitions.Def_Submission_ThreeSum_ColorBandBounds
import Theorems.Thm_ThreeSum_BandPartition_size_mono
import Theorems.Thm_ThreeSum_LightBandEnumeration_width_mono


set_option autoImplicit false
open ThreeSum ThreeSum.ColorBandBounds
open BandPartition
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
namespace ThreeSum.ColorBandBounds
theorem _root_.solution {a b c n g : ℕ} (hlen : a+b+c=n) :
    LightBandEnumeration.width (size a g) (size b g) (size c g) ≤ width n g :=
  LightBandEnumeration.width_mono (size_mono (by omega : a ≤ n))
    (size_mono (by omega : b ≤ n)) (size_mono (by omega : c ≤ n))
end ThreeSum.ColorBandBounds
