-- Prove2me | solution 1 for ThreeSum.LightWeightedFrozenQuery.program_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:31:13.207532+00:00
-- url     : https://prove2.me/submissions/2a277698-6c65-45c2-9d14-13ec5eed1315

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_Weighted_Frozen

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open Light
namespace ThreeSum.LightWeightedFrozenQuery
theorem _root_.solution : program[2]? = some (LightBandLookup.searchBody 2) := rfl
end ThreeSum.LightWeightedFrozenQuery
