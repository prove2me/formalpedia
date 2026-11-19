-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch43_440
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:11.217495+00:00
-- url     : https://prove2.me/submissions/501f1b4a-e7e2-4c9d-9675-e5e8d7ca3cdd

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 19 9 degreeUnionState43_440 [9,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
