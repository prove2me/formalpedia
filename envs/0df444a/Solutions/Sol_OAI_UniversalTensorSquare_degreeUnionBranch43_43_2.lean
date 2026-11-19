-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch43_43
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:24.976217+00:00
-- url     : https://prove2.me/submissions/a7afebb3-13be-46ac-807e-9c75f360b5cb

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 21 10 degreeUnionState43_43 [10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
