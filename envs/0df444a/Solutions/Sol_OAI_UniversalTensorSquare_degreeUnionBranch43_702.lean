-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_702
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:33:30.747067+00:00
-- url     : https://prove2.me/submissions/d941946c-fb82-469e-88d1-f2f010c86b02

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 30 13 degreeUnionState43_702 [13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
