-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_685
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:33:43.607113+00:00
-- url     : https://prove2.me/submissions/9e5d32c6-e2d3-427a-8a51-c93ae540d100

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 39 4 degreeUnionState43_685 [4] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
