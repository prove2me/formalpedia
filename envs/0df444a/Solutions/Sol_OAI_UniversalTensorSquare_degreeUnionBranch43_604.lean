-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_604
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:37.317877+00:00
-- url     : https://prove2.me/submissions/8d8e3f66-6fba-4706-b318-e4d955463102

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 7 36 degreeUnionState43_604 [36] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
