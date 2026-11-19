-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch43_437
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:17.507351+00:00
-- url     : https://prove2.me/submissions/5e750261-e1d7-43bf-b9b8-16142acfca70

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 22 6 degreeUnionState43_437 [6,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
