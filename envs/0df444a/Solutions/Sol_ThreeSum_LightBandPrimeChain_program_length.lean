-- Prove2me | solution 1 for ThreeSum.LightBandPrimeChain.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:57:10.964014+00:00
-- url     : https://prove2.me/submissions/ec51e18d-27d6-4be8-bb0a-54a6c4d5f04d

import Definitions.Def_Submission_ThreeSum_LightBandPrimeMinimum
import Definitions.Def_Submission_ThreeSum_LightBandPrimeChain

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeChain
open Light BandCandidateRows BandPrimeChoice
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
namespace ThreeSum.LightBandPrimeChain
theorem _root_.solution : program.length=19 := rfl
end ThreeSum.LightBandPrimeChain
