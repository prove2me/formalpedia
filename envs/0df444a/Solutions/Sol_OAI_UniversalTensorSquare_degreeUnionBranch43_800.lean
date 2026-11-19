-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_800
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:42:50.962646+00:00
-- url     : https://prove2.me/submissions/c5f57bbd-f77c-43d1-82aa-6b555fdb947a

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 13 30 degreeUnionState43_800 [30] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
