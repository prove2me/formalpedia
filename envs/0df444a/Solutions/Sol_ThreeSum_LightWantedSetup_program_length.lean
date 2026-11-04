-- Prove2me | solution 1 for ThreeSum.LightWantedSetup.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:11:37.657175+00:00
-- url     : https://prove2.me/submissions/11a7da4a-17d4-469b-9b98-49e151a6b37e

import Definitions.Def_Submission_ThreeSum_LightWantedJoin
import Definitions.Def_Submission_ThreeSum_WantedResidueKeys
import Definitions.Def_Submission_ThreeSum_LightSourceBucketSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightWantedSetup

set_option autoImplicit false
open ThreeSum ThreeSum.LightWantedSetup
open Light WantedResidueKeys
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
namespace ThreeSum.LightWantedSetup
theorem _root_.solution : program.length=12 := rfl
end ThreeSum.LightWantedSetup
