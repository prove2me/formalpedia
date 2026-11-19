-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_678
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:33:53.599665+00:00
-- url     : https://prove2.me/submissions/e6855c25-41f0-4480-80f2-8e1ae38bd6b5

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 6 37 degreeUnionState43_678 [37] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
