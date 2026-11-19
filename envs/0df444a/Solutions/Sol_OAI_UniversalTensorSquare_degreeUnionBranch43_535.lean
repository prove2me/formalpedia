-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_535
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:12.822849+00:00
-- url     : https://prove2.me/submissions/6065d8c4-89a9-42fd-a80c-d4f21b011d43

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 1 42 degreeUnionState43_535 [42] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
