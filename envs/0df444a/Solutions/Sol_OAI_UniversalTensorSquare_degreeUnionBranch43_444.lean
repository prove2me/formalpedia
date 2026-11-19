-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_444
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:00.993037+00:00
-- url     : https://prove2.me/submissions/3c31dd81-8759-4dce-b86a-4813d7c52e0c

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 15 13 degreeUnionState43_444 [13,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
