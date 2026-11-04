-- Prove2me | solution 1 for ThreeSum.EncodedColorPrimeCosts.space_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:41:44.066197+00:00
-- url     : https://prove2.me/submissions/591d36b4-abad-4386-b40e-98014cf78d97

import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrime
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeCosts

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPrimeCosts
open Light Scales BandScales CostLedger ArithmeticStageBounds
namespace ThreeSum.EncodedColorPrimeCosts
theorem _root_.solution (free maxMod g M y U : ℕ) :
    LightEncodedColorPrimeCore.space free maxMod g M y U=
      LightBandPrimeSetup.space (EncodedColorPrimeData.poolBase free) maxMod g M y U := rfl
end ThreeSum.EncodedColorPrimeCosts
