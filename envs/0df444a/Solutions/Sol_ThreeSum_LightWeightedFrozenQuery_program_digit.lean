-- Prove2me | solution 1 for ThreeSum.LightWeightedFrozenQuery.program_digit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:32:20.417393+00:00
-- url     : https://prove2.me/submissions/3d512ab4-3908-4148-bfe9-c463403f28f1

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_Weighted_Frozen

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open Light
namespace ThreeSum.LightWeightedFrozenQuery
theorem _root_.solution : program[3]? = some (LightTernaryCodes.digitBody 5) := rfl
end ThreeSum.LightWeightedFrozenQuery
