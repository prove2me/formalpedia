-- Prove2me | solution 1 for ThreeSum.LightGuardedWanted.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:31:11.876486+00:00
-- url     : https://prove2.me/submissions/980e9b25-3e2e-4b25-9e12-dad0fc610680

import Definitions.Def_Submission_ThreeSum_LightCoverKeyData
import Definitions.Def_Submission_ThreeSum_LightRawAKeys
import Definitions.Def_Submission_ThreeSum_LightBalancedWanted
import Definitions.Def_Submission_ThreeSum_LightGuardedWanted

set_option autoImplicit false
open ThreeSum ThreeSum.LightGuardedWanted
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
namespace ThreeSum.LightGuardedWanted
theorem _root_.solution : program.length=99 := rfl
end ThreeSum.LightGuardedWanted
