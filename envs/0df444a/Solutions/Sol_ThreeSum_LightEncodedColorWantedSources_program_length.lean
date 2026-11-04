-- Prove2me | solution 1 for ThreeSum.LightEncodedColorWantedSources.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:32:21.888494+00:00
-- url     : https://prove2.me/submissions/77f08d45-63fb-4c3a-9d91-d895d6b440fa

import Definitions.Def_Submission_ThreeSum_LightEncodedColorFiniteSources
import Definitions.Def_Submission_ThreeSum_LightEncodedColorWantedSources

set_option autoImplicit false
open ThreeSum ThreeSum.LightEncodedColorWantedSources
open Light Scales TrimScales BandScales
set_option maxHeartbeats 2500000
set_option maxRecDepth 13000
namespace ThreeSum.LightEncodedColorWantedSources
theorem _root_.solution : program.length=181 := rfl
end ThreeSum.LightEncodedColorWantedSources
