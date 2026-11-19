-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch43_443
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:12.125746+00:00
-- url     : https://prove2.me/submissions/1095c791-160d-46e2-ae77-e371008f44b7

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 16 12 degreeUnionState43_443 [12,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
