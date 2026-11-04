-- Prove2me | solution 1 for ThreeSum.LightWeightedFrozenQuery.program_main
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:42:38.021201+00:00
-- url     : https://prove2.me/submissions/c53b0263-0430-41eb-93e2-c97d0cb5d000

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_Weighted_Frozen

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open Light
namespace ThreeSum.LightWeightedFrozenQuery
theorem _root_.solution : program[0]? = some (body 0 1 3 4 5) := rfl
end ThreeSum.LightWeightedFrozenQuery
