-- Prove2me | solution 1 for ThreeSum.LightEncodedColorPrimeHost.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:27:08.849233+00:00
-- url     : https://prove2.me/submissions/41deda5c-54e9-44f2-adcd-fab98dda17df

import Definitions.Def_Submission_ThreeSum_LightEncodedColorNormalize
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeHost

set_option autoImplicit false
open ThreeSum ThreeSum.LightEncodedColorPrimeHost
open Light Scales BandScales ArithmeticStageBounds ColorClassLists EncodedColorLayout
set_option maxHeartbeats 3200000
set_option maxRecDepth 15000
namespace ThreeSum.LightEncodedColorPrimeHost
theorem _root_.solution : program.length=72 := rfl
end ThreeSum.LightEncodedColorPrimeHost
