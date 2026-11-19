-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_35
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:49:40.688451+00:00
-- url     : https://prove2.me/submissions/8d0b9460-1430-4183-ba4f-0df761fd373b

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 45 13 degreeUnionState58_35 [13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
