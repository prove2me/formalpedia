-- Prove2me | solution 1 for ThreeSum.LightBandRawAResources.word_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:03:38.326198+00:00
-- url     : https://prove2.me/submissions/2ea2decd-712a-43cc-9a33-8586cb304be2

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_LightBandRawAResources
import Theorems.Thm_ThreeSum_BandPartition_size_le
import Theorems.Thm_ThreeSum_LightPrimePool_size_le


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAResources
open Light EncodedColorLayout
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
namespace ThreeSum.LightBandRawAResources
theorem _root_.solution (W n g U : ℕ) :
    LightBandRawAColor.word W n g U ≤ 2^(W+1)+3*n^2+29*n+2*g+9*U+100 := by
  have hm := BandPartition.size_le n g
  have hq := Nat.pow_le_pow_left hm 2
  unfold LightBandRawAColor.word LightColorBands.word ColorBandBounds.word
    LightBandEnumeration.word LightBandRawACatalog.word LightBandCandidates.word
    LightBandRawA.word LightBandEnumeration.count
  nlinarith only [hm,hq]
end ThreeSum.LightBandRawAResources
