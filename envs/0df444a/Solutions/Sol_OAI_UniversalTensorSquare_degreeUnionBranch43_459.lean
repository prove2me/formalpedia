-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_459
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:06.897209+00:00
-- url     : https://prove2.me/submissions/400ab346-10c2-4300-b89e-40a1d8ae37c4

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 13 14 degreeUnionState43_459 [14,16] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
