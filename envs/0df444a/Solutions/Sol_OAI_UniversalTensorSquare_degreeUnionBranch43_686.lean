-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_686
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:33:47.629051+00:00
-- url     : https://prove2.me/submissions/15c21833-7e57-48e9-8fa6-192369bcf01c

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 38 5 degreeUnionState43_686 [5] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
