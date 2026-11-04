-- Prove2me | solution 1 for ThreeSum.LightBandPrimeSetup.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:16:54.515243+00:00
-- url     : https://prove2.me/submissions/381ff858-f004-4147-92b6-f5ebb287f723

import Definitions.Def_Submission_ThreeSum_LightBandPrimeDepth
import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeSetup
open Light BandCandidateRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000
namespace ThreeSum.LightBandPrimeSetup
theorem _root_.solution : program.length=25 := rfl
end ThreeSum.LightBandPrimeSetup
