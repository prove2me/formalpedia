-- Prove2me | solution 1 for ThreeSum.LightTernaryFrozenQuery.program_lookup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:39:18.5169+00:00
-- url     : https://prove2.me/submissions/158c60d7-1294-4618-8c89-370e0bffa34b

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQuery

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open Light
namespace ThreeSum.LightTernaryFrozenQuery
theorem _root_.solution : program[1]? = some (LightTernaryQueryLookup.body 2) := rfl
end ThreeSum.LightTernaryFrozenQuery
