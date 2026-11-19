-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch43_438
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:18.442006+00:00
-- url     : https://prove2.me/submissions/4ed50178-45af-4ed5-85af-feec8a86881b

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 21 7 degreeUnionState43_438 [7,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
