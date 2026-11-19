-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_594
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:44.132562+00:00
-- url     : https://prove2.me/submissions/2b85025f-0bfc-4356-9b51-6724fe7ccb17

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 17 26 degreeUnionState43_594 [26] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
