-- Prove2me | solution 1 for ThreeSum.LightWeightedFrozenQuery.program_lookup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:31:09.720488+00:00
-- url     : https://prove2.me/submissions/697ca496-c05d-4108-9b93-fbf09bdcaddb

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_Weighted_Frozen

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open Light
namespace ThreeSum.LightWeightedFrozenQuery
theorem _root_.solution : program[1]? = some (LightTernaryQueryLookup.body 2) := rfl
end ThreeSum.LightWeightedFrozenQuery
