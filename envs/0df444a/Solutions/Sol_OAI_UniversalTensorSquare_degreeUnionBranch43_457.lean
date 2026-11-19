-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_457
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:04.568373+00:00
-- url     : https://prove2.me/submissions/82e2d25a-363c-4e06-b275-1a887be3f026

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 15 12 degreeUnionState43_457 [12,16] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
