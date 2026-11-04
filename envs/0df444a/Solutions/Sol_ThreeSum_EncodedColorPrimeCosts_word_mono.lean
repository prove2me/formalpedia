-- Prove2me | solution 1 for ThreeSum.EncodedColorPrimeCosts.word_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:47:45.290742+00:00
-- url     : https://prove2.me/submissions/aa0a63a0-5b80-4dac-8eeb-c5da0f64bc8d

import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrime
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeCosts
import Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_count_mono
import Theorems.Thm_ThreeSum_BandRawA_count_mono
import Theorems.Thm_ThreeSum_LightBandEnumeration_count_mono
import Theorems.Thm_ThreeSum_SourceBuckets_count_mono
import Theorems.Thm_ThreeSum_WantedPairs_count_mono


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPrimeCosts
open Light Scales BandScales CostLedger ArithmeticStageBounds
namespace ThreeSum.EncodedColorPrimeCosts
theorem _root_.solution {maxMod nA nB nC nA' nB' nC' g M y U : ℕ}
    (ha : nA ≤ nA') (hb : nB ≤ nB') (hc : nC ≤ nC') :
    LightEncodedColorPrime.word maxMod nA nB nC g M y U ≤
      LightEncodedColorPrime.word maxMod nA' nB' nC' g M y U := by
  have hR := count_mono (g := g) ha hb hc
  have hmul := Nat.mul_le_mul_right (LightPrimePool.size y*g^3) hR
  unfold LightEncodedColorPrime.word LightEncodedColorPrimeCore.word
    LightBandWeightedScore.word LightBandWeightedScoreCell.word
  omega
end ThreeSum.EncodedColorPrimeCosts
