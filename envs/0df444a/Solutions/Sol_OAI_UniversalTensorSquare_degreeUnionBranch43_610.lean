-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_610
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:28.504514+00:00
-- url     : https://prove2.me/submissions/d9539c9e-e053-4926-8184-c3b60996c5d8

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 1 42 degreeUnionState43_610 [42] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
