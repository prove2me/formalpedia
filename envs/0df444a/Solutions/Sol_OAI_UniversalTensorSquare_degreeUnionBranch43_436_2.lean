-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch43_436
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:22.152766+00:00
-- url     : https://prove2.me/submissions/606a96c4-7b67-4fed-b432-e7f6f7339894

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 23 5 degreeUnionState43_436 [5,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
