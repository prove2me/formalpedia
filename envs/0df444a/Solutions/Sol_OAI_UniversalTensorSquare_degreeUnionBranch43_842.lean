-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_842
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:10:25.471427+00:00
-- url     : https://prove2.me/submissions/9f60b561-01b1-458f-a5f0-d1f67684ed0f

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 12 31 degreeUnionState43_842 [31] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
