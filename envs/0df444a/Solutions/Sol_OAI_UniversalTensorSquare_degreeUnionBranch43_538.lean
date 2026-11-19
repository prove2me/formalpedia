-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_538
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:11.902308+00:00
-- url     : https://prove2.me/submissions/c1606054-2b70-4d69-9f95-3d0e04a8f06a

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 38 5 degreeUnionState43_538 [5] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
