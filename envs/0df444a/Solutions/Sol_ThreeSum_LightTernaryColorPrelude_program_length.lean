-- Prove2me | solution 1 for ThreeSum.LightTernaryColorPrelude.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:40:27.140056+00:00
-- url     : https://prove2.me/submissions/189544d9-2462-4156-843f-108fdeee2a59

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightColorScanHost
import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryColorPrelude
open Light ColorClassLists LightColorParametersCosts
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryColorPrelude
theorem _root_.solution : program.length=28 :=rfl
end ThreeSum.LightTernaryColorPrelude
