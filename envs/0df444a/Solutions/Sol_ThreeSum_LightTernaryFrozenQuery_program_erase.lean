-- Prove2me | solution 1 for ThreeSum.LightTernaryFrozenQuery.program_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:39:36.059711+00:00
-- url     : https://prove2.me/submissions/078b5958-52df-46f3-a0bc-8030c8a72c67

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQuery

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open Light
namespace ThreeSum.LightTernaryFrozenQuery
theorem _root_.solution : program[5]? = some (LightMaskErase.body 5) := rfl
end ThreeSum.LightTernaryFrozenQuery
