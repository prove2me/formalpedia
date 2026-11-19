-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_71
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:33:34.731427+00:00
-- url     : https://prove2.me/submissions/39da1a2a-4d2b-4df8-bb9a-41bb7cb9c167

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 21 7 degreeUnionState43_71 [7,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
