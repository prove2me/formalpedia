-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_877
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:46.454202+00:00
-- url     : https://prove2.me/submissions/385291b7-b223-45f8-873a-812e96753085

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 16 18 25 degreeUnionState43_877 [25] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
