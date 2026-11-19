-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch43_442
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:13.150422+00:00
-- url     : https://prove2.me/submissions/c4cc1572-0233-436c-b773-e2e52d043e0e

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 17 11 degreeUnionState43_442 [11,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
