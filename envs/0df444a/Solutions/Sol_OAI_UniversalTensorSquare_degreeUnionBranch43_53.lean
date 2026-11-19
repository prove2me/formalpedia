-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_53
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:15.711784+00:00
-- url     : https://prove2.me/submissions/255bb579-e419-46d4-9397-ed2976f80183

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 19 11 degreeUnionState43_53 [11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
