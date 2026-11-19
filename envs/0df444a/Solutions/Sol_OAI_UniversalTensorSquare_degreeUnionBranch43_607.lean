-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_607
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:38.176011+00:00
-- url     : https://prove2.me/submissions/59e5496d-f47e-4123-8d19-5016e82992c6

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 4 39 degreeUnionState43_607 [39] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
