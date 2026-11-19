-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_681
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:33:55.386986+00:00
-- url     : https://prove2.me/submissions/b46a39b0-9db2-43ed-bc21-2dfbb95c9f86

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 3 40 degreeUnionState43_681 [40] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
