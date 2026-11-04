-- Prove2me | solution 1 for ThreeSum.LightEncodedColorPrime.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:12:14.277308+00:00
-- url     : https://prove2.me/submissions/95008b82-0a8f-4eda-8b6c-80fa5ed1785e

import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeCore
import Definitions.Def_Submission_ThreeSum_SourceFiniteRetention
import Definitions.Def_Submission_ThreeSum_LightBandPrimeStage
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrime

set_option autoImplicit false
open ThreeSum ThreeSum.LightEncodedColorPrime
open Light BandPartition BandCandidateRows BandRawA SourceFiniteInputs
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
namespace ThreeSum.LightEncodedColorPrime
theorem _root_.solution : program.length=25 := rfl
end ThreeSum.LightEncodedColorPrime
