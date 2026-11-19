-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_527
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:24.137983+00:00
-- url     : https://prove2.me/submissions/975094a4-54f4-4da8-b72e-5e6775741a05

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 9 34 degreeUnionState43_527 [34] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
