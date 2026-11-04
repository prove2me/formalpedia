-- Prove2me | solution 1 for ThreeSum.ColorBandBounds.depth_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:02:28.339701+00:00
-- url     : https://prove2.me/submissions/0c164d08-6e1a-4f94-9973-0d7e22579fe3

import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
import Definitions.Def_Submission_ThreeSum_ColorBandBounds
import Theorems.Thm_ThreeSum_ColorBandBounds_width_le

set_option autoImplicit false
open ThreeSum ThreeSum.ColorBandBounds
open BandPartition
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
namespace ThreeSum.ColorBandBounds
theorem _root_.solution {a b c n g : ℕ} (hlen : a+b+c=n) :
    LightBandPreprocessing.depth a b c g ≤ depth n g := by
  have hw := width_le (g := g) hlen
  unfold LightBandPreprocessing.depth depth
  rw [hlen]
  omega
end ThreeSum.ColorBandBounds
