-- Prove2me | solution 1 for ThreeSum.EncodedColorPrimeCosts.time_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:52:34.743204+00:00
-- url     : https://prove2.me/submissions/b5f2c7e2-41b8-4cae-a1cb-c95cb4833df4

import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrime
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeCosts
import Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_core_time_eq

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPrimeCosts
open Light Scales BandScales CostLedger ArithmeticStageBounds
namespace ThreeSum.EncodedColorPrimeCosts
theorem _root_.solution (maxMod nA nB nC g M y U : ℕ) :
    LightEncodedColorPrime.time maxMod nA nB nC g M y U=
      LightBandPrimeSetup.time maxMod g (LightEncodedColorPrime.count nA nB nC g) M y U+1160 := by
  rw [LightEncodedColorPrime.time,core_time_eq]
end ThreeSum.EncodedColorPrimeCosts
