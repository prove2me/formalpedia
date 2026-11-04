-- Prove2me | solution 1 for ThreeSum.LightWeightedFrozenQuery.program_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:06.446488+00:00
-- url     : https://prove2.me/submissions/6a7e365d-ec86-42a7-b669-8c79f369b688

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_Weighted_Frozen

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open Light
namespace ThreeSum.LightWeightedFrozenQuery
theorem _root_.solution : program[4]? = some (LightTernaryCodes.zeroBody 5) := rfl
end ThreeSum.LightWeightedFrozenQuery
