-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_518
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:48.94274+00:00
-- url     : https://prove2.me/submissions/2998252e-55cd-4190-bcfa-23ebfaa7eb25

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 18 25 degreeUnionState43_518 [25] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
