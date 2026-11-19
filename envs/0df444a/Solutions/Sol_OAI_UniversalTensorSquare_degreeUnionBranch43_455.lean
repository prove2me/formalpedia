-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_455
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:05.581755+00:00
-- url     : https://prove2.me/submissions/0840f6c6-0424-464b-bd50-729553038a4d

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 17 10 degreeUnionState43_455 [10,16] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
