-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_683
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:33:39.081497+00:00
-- url     : https://prove2.me/submissions/8f8a886a-d76f-4cd4-9067-c1e391291085

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 1 42 degreeUnionState43_683 [42] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
