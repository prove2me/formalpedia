-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_595
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:47.887842+00:00
-- url     : https://prove2.me/submissions/a6b85a9e-d090-4826-ac14-afa5eef2e3c4

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 16 27 degreeUnionState43_595 [27] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
