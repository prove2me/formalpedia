-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_878
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:45.462058+00:00
-- url     : https://prove2.me/submissions/acbacbb2-fcf1-45a1-9e4d-5d51b54ad3ea

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 16 17 26 degreeUnionState43_878 [26] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
