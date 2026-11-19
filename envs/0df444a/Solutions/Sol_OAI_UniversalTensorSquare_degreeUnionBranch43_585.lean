-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_585
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:57.778868+00:00
-- url     : https://prove2.me/submissions/3e432695-8a75-4c36-8b0d-e379fd50715d

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 26 17 degreeUnionState43_585 [17] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
