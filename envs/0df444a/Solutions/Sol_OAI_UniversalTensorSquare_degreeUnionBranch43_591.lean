-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_591
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:50.775936+00:00
-- url     : https://prove2.me/submissions/0c203d4d-ec3d-47fc-87c4-6a099ca1fb05

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 20 23 degreeUnionState43_591 [23] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
