-- Prove2me | solution 1 for ThreeSum.LightEncodedColorPrimeCore.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:17:23.871991+00:00
-- url     : https://prove2.me/submissions/81283415-b2ca-4761-8ff1-ffff85d69708

import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeData
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeCore

set_option autoImplicit false
open ThreeSum ThreeSum.LightEncodedColorPrimeCore
open Light BandCandidateRows EncodedColorPrimeData
set_option maxHeartbeats 2600000
set_option maxRecDepth 13000
namespace ThreeSum.LightEncodedColorPrimeCore
theorem _root_.solution : program.length=24 := rfl
end ThreeSum.LightEncodedColorPrimeCore
