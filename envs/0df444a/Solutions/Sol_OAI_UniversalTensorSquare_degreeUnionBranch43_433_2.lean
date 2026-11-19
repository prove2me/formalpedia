-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch43_433
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:22.928961+00:00
-- url     : https://prove2.me/submissions/36aeca2a-968f-49a7-83bf-4402bafbcf1b

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniversalTensorSquare

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 15 14 degreeUnionState43_433 [14,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
