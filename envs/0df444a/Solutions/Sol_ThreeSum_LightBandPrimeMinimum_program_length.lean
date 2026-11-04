-- Prove2me | solution 1 for ThreeSum.LightBandPrimeMinimum.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:47:59.78593+00:00
-- url     : https://prove2.me/submissions/672d5f2d-d0b5-45cf-b2b3-10df8609874f

import Definitions.Def_Submission_ThreeSum_LightBandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandPrimeChoice
import Definitions.Def_Submission_ThreeSum_LightBandPrimeMinimum

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeMinimum
open Light BandCandidateRows BandWeightedScore BandPrimeChoice
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
namespace ThreeSum.LightBandPrimeMinimum
theorem _root_.solution : program.length=18 := rfl
end ThreeSum.LightBandPrimeMinimum
