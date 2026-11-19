-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_55
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:06.389084+00:00
-- url     : https://prove2.me/submissions/4a61a965-37b8-41de-8df0-d8d68fa3a581

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 17 13 degreeUnionState43_55 [13,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
