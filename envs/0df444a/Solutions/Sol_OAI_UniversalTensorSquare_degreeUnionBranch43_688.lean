-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_688
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:33:41.165503+00:00
-- url     : https://prove2.me/submissions/273cf51f-6923-471d-9c11-7d9fd729389d

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 36 7 degreeUnionState43_688 [7] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
