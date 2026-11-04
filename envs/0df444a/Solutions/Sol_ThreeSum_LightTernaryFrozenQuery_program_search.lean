-- Prove2me | solution 1 for ThreeSum.LightTernaryFrozenQuery.program_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:39:31.444366+00:00
-- url     : https://prove2.me/submissions/73690711-8da0-4d35-a076-3cd3e445179c

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQuery

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open Light
namespace ThreeSum.LightTernaryFrozenQuery
theorem _root_.solution : program[2]? = some (LightBandLookup.searchBody 2) := rfl
end ThreeSum.LightTernaryFrozenQuery
