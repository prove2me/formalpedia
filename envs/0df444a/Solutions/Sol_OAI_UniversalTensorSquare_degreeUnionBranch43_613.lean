-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_613
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:34.544733+00:00
-- url     : https://prove2.me/submissions/62bd9084-1644-4889-bc9e-1c1bc5713fbd

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 38 5 degreeUnionState43_613 [5] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
