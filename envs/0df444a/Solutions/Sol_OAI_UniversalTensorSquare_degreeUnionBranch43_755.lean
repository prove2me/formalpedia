-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_755
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:37:25.882671+00:00
-- url     : https://prove2.me/submissions/02da0146-7f2b-4a59-9f34-4e9299684b59

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 17 26 degreeUnionState43_755 [26] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
