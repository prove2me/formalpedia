-- Prove2me | solution 1 for ThreeSum.EncodedColorPrimeCosts.core_time_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:38:07.047405+00:00
-- url     : https://prove2.me/submissions/ad30cb69-bbb0-4d6c-be19-43015db8e5ce

import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrime
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeCosts

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPrimeCosts
open Light Scales BandScales CostLedger ArithmeticStageBounds
namespace ThreeSum.EncodedColorPrimeCosts
theorem _root_.solution (maxMod g R M y U : ℕ) :
    LightEncodedColorPrimeCore.time maxMod g R M y U=
      LightBandPrimeSetup.time maxMod g R M y U+760 := by
  unfold LightEncodedColorPrimeCore.time LightBandPrimeSetup.time LightBandPrimeConstruction.time
  omega
end ThreeSum.EncodedColorPrimeCosts
