-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_70
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:33:42.514477+00:00
-- url     : https://prove2.me/submissions/97b6b214-405d-4949-bdf4-ec992049f32f

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 22 6 degreeUnionState43_70 [6,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
