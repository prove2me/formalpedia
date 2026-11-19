-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_705
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:33:37.81851+00:00
-- url     : https://prove2.me/submissions/14536b18-ff9e-4d88-822e-1ee621fae5d3

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 27 16 degreeUnionState43_705 [16] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
