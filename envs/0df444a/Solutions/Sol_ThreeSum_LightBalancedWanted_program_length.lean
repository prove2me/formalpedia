-- Prove2me | solution 1 for ThreeSum.LightBalancedWanted.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:21:15.197118+00:00
-- url     : https://prove2.me/submissions/feb3e35a-3c3a-4bb0-a99e-0aeaed6b90e3

import Definitions.Def_Submission_ThreeSum_LightWantedSetup
import Definitions.Def_Submission_ThreeSum_LightBalancedWanted

set_option autoImplicit false
open ThreeSum ThreeSum.LightBalancedWanted
open Light WantedResidueKeys
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace ThreeSum.LightBalancedWanted
theorem _root_.solution : program.length=26 := rfl
end ThreeSum.LightBalancedWanted
