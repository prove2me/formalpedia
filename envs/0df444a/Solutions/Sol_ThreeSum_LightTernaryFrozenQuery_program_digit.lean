-- Prove2me | solution 1 for ThreeSum.LightTernaryFrozenQuery.program_digit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:39:32.812343+00:00
-- url     : https://prove2.me/submissions/65f9b365-0dc7-446b-b1ec-710ad1790286

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQuery

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open Light
namespace ThreeSum.LightTernaryFrozenQuery
theorem _root_.solution : program[3]? = some (LightTernaryCodes.digitBody 5) := rfl
end ThreeSum.LightTernaryFrozenQuery
