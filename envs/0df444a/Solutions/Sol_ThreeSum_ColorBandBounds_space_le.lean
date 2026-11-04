-- Prove2me | solution 1 for ThreeSum.ColorBandBounds.space_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:39:06.195103+00:00
-- url     : https://prove2.me/submissions/bab22ee5-90ae-49d8-8aef-982245f1228c

import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
import Definitions.Def_Submission_ThreeSum_ColorBandBounds
import Theorems.Thm_ThreeSum_ColorBandBounds_count_le
import Theorems.Thm_ThreeSum_ColorBandBounds_width_le

set_option autoImplicit false
open ThreeSum ThreeSum.ColorBandBounds
open BandPartition
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
namespace ThreeSum.ColorBandBounds
theorem _root_.solution {a b c n g work : ℕ} (hlen : a+b+c=n) :
    LightBandPreprocessing.space work a b c g ≤ space work n g := by
  have hc := count_le (g := g) hlen
  have hw := width_le (g := g) hlen
  unfold LightBandPreprocessing.space space
  omega
end ThreeSum.ColorBandBounds
