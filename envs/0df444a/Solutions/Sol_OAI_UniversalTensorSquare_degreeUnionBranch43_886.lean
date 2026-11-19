-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_886
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T04:33:17.162132+00:00
-- url     : https://prove2.me/submissions/60b2197d-94cf-49a5-9407-ce260d16f42c

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 16 9 34 degreeUnionState43_886 [34] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
