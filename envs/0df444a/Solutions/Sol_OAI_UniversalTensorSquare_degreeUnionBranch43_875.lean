-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_875
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:10:20.604208+00:00
-- url     : https://prove2.me/submissions/e29cccff-fa77-4a0d-a46b-c760b07bdf53

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 16 20 23 degreeUnionState43_875 [23] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
