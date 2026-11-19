-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_528
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:21.502515+00:00
-- url     : https://prove2.me/submissions/bfc761f6-1dd5-45f3-80d1-b9b8a853c849

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 8 35 degreeUnionState43_528 [35] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
