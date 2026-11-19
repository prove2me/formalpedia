-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_799
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:42:51.935298+00:00
-- url     : https://prove2.me/submissions/5c343fa4-7344-43cd-bf83-a0ab99a7e60b

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 14 29 degreeUnionState43_799 [29] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
