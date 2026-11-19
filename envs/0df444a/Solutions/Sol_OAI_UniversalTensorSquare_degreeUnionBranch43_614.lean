-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_614
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:26.903242+00:00
-- url     : https://prove2.me/submissions/768e01ac-5a24-49a1-9018-a1c015bcfc49

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 37 6 degreeUnionState43_614 [6] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
