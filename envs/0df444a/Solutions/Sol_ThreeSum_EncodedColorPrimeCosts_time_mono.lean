-- Prove2me | solution 1 for ThreeSum.EncodedColorPrimeCosts.time_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:04:35.58621+00:00
-- url     : https://prove2.me/submissions/4bd4db83-abd5-4041-8f7b-0f0a86ea46c0

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
    LightEncodedColorPrime.time maxMod nA nB nC g M y U ≤
      LightEncodedColorPrime.time maxMod nA' nB' nC' g M y U := by
  have hR := count_mono (g := g) ha hb hc
  unfold LightEncodedColorPrime.time LightEncodedColorPrimeCore.time LightBandPrimeChain.time
    LightBandPrimeMinimum.time LightBandWeightedScore.time
  gcongr
end ThreeSum.EncodedColorPrimeCosts
