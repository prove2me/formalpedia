-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_531
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:17.532843+00:00
-- url     : https://prove2.me/submissions/3c78b128-1b1e-46db-b8ec-9318d0fc9212

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 5 38 degreeUnionState43_531 [38] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
