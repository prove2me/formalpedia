-- Prove2me | solution 1 for ThreeSum.LightWeightedFrozenQuery.program_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:14.639747+00:00
-- url     : https://prove2.me/submissions/9e5b427c-4313-465f-8bec-c1564a916429

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_Weighted_Frozen

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open Light
namespace ThreeSum.LightWeightedFrozenQuery
theorem _root_.solution : program[5]? = some (LightMaskErase.body 5) := rfl
end ThreeSum.LightWeightedFrozenQuery
