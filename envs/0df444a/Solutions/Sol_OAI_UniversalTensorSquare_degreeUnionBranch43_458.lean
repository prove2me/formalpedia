-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_458
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:02.81882+00:00
-- url     : https://prove2.me/submissions/6737199e-020b-4ba3-8a6c-e961a3465413

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 14 13 degreeUnionState43_458 [13,16] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
