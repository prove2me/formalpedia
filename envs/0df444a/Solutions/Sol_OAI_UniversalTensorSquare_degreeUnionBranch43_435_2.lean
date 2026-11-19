-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch43_435
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:20.352516+00:00
-- url     : https://prove2.me/submissions/1d8a8142-53ec-4cb3-bce0-94aca9bffd2f

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 24 4 degreeUnionState43_435 [4,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
