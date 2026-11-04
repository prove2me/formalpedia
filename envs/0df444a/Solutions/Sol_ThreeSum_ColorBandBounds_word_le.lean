-- Prove2me | solution 1 for ThreeSum.ColorBandBounds.word_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:53:26.367439+00:00
-- url     : https://prove2.me/submissions/0e29c147-46e7-4964-b4f4-3b6da5b625d8

import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
import Definitions.Def_Submission_ThreeSum_ColorBandBounds
import Theorems.Thm_ThreeSum_BandPartition_size_mono


set_option autoImplicit false
open ThreeSum ThreeSum.ColorBandBounds
open BandPartition
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
namespace ThreeSum.ColorBandBounds
theorem _root_.solution {a b c n g U : ℕ} (hlen : a+b+c=n) :
    LightBandPreprocessing.word a b c g U ≤ word n g U := by
  have ha := size_mono (g := g) (by omega : a ≤ n)
  have hb := size_mono (g := g) (by omega : b ≤ n)
  have hc := size_mono (g := g) (by omega : c ≤ n)
  unfold LightBandPreprocessing.word word LightBandEnumeration.word
  omega
end ThreeSum.ColorBandBounds
