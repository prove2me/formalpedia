-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_615
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:32.38673+00:00
-- url     : https://prove2.me/submissions/0f247540-2d0c-4c4f-acb9-c7b8ad52151c

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 36 7 degreeUnionState43_615 [7] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
