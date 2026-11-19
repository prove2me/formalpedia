-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_533
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:08.330833+00:00
-- url     : https://prove2.me/submissions/30f6be49-e0eb-4803-b7c1-6c8ccc78e0bc

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 3 40 degreeUnionState43_533 [40] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
