-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_583
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:56.722255+00:00
-- url     : https://prove2.me/submissions/3287603a-116f-4076-aaa2-d8b38f06a817

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 28 15 degreeUnionState43_583 [15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
