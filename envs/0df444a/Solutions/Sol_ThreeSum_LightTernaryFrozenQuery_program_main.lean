-- Prove2me | solution 1 for ThreeSum.LightTernaryFrozenQuery.program_main
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:54:51.381468+00:00
-- url     : https://prove2.me/submissions/e88fbd4e-6422-4b8e-831a-2106cf813ac7

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQuery

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open Light
namespace ThreeSum.LightTernaryFrozenQuery
theorem _root_.solution : program[0]? = some (body 0 1 3 4 5) := rfl
end ThreeSum.LightTernaryFrozenQuery
