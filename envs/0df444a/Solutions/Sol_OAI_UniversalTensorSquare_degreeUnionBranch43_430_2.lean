-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch43_430
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:19.333202+00:00
-- url     : https://prove2.me/submissions/7dd62bfb-98ba-463d-a10b-026be4fcf5d9

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 18 11 degreeUnionState43_430 [11,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
