-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_456
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:00.051293+00:00
-- url     : https://prove2.me/submissions/61b77540-e4a6-476b-8537-b4a5013a68ad

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 16 11 degreeUnionState43_456 [11,16] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
