-- Prove2me | solution 1 for ThreeSum.LightEncodedColorSources.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:07:15.741201+00:00
-- url     : https://prove2.me/submissions/0d6e60f3-a8ef-4618-b1c4-d764c2feb4ef

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedData
import Definitions.Def_Submission_ThreeSum_EncodedColorCoverData
import Definitions.Def_Submission_ThreeSum_LightSourceFinitePrepared
import Definitions.Def_Submission_ThreeSum_LightEncodedColorSources

set_option autoImplicit false
open ThreeSum ThreeSum.LightEncodedColorSources
open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding SourceFiniteInputs
set_option maxHeartbeats 2600000
set_option maxRecDepth 14000
namespace ThreeSum.LightEncodedColorSources
theorem _root_.solution : program.length=81 := rfl
end ThreeSum.LightEncodedColorSources
