-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch43_441
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:13.957533+00:00
-- url     : https://prove2.me/submissions/3cb7f604-7a2b-479a-8d14-1c425d723ba4

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 18 10 degreeUnionState43_441 [10,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
