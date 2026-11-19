-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_835
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:42:41.318796+00:00
-- url     : https://prove2.me/submissions/6a929197-e628-4811-a088-b630c59e167d

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 19 24 degreeUnionState43_835 [24] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
