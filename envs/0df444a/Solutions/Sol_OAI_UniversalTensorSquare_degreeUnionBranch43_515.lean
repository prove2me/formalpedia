-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_515
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:49.84471+00:00
-- url     : https://prove2.me/submissions/4378b1db-0f5f-4f5f-bbb9-b484abdad8bc

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 21 22 degreeUnionState43_515 [22] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
