-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_448
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:10.262858+00:00
-- url     : https://prove2.me/submissions/e8952f97-ec4a-4f97-aebc-be6c5974a556

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 24 3 degreeUnionState43_448 [3,16] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
