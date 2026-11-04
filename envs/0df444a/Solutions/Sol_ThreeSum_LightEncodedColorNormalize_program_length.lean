-- Prove2me | solution 1 for ThreeSum.LightEncodedColorNormalize.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:03:32.452186+00:00
-- url     : https://prove2.me/submissions/a68474c8-8fb7-4418-9708-c306054d42af

import Definitions.Def_Submission_ThreeSum_EncodedColorNormalizedData
import Definitions.Def_Submission_ThreeSum_LightEncodedColorLayout
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightEncodedColorNormalize

set_option autoImplicit false
open ThreeSum ThreeSum.LightEncodedColorNormalize
open Light Scales BandScales ColorClassLists EncodedColorLayout EncodedColorNormalizedData
set_option maxHeartbeats 2600000
set_option maxRecDepth 14000
namespace ThreeSum.LightEncodedColorNormalize
theorem _root_.solution : program.length=46 := rfl
end ThreeSum.LightEncodedColorNormalize
