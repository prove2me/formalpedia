-- Prove2me | solution 1 for ThreeSum.LightTernaryFrozenQuery.program_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:39:34.385241+00:00
-- url     : https://prove2.me/submissions/31a9b412-aa1a-4e0d-809f-dbbe8eced51a

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQuery

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open Light
namespace ThreeSum.LightTernaryFrozenQuery
theorem _root_.solution : program[4]? = some (LightTernaryCodes.zeroBody 5) := rfl
end ThreeSum.LightTernaryFrozenQuery
