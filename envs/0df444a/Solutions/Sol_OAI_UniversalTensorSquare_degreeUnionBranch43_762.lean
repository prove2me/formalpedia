-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_762
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:37:22.031696+00:00
-- url     : https://prove2.me/submissions/0f918d8a-f644-4047-9b54-f23ea0745d32

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 10 33 degreeUnionState43_762 [33] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
