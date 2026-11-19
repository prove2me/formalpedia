-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch43_429
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:23.851484+00:00
-- url     : https://prove2.me/submissions/3590fa83-88b3-41ae-a64e-afab37b3c105

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 19 10 degreeUnionState43_429 [10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
