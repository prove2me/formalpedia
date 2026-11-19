-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_609
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:29.472672+00:00
-- url     : https://prove2.me/submissions/4efd3691-d7a6-4e1a-8b30-75e8cf1a7637

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 2 41 degreeUnionState43_609 [41] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
