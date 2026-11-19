-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_602
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:45.98383+00:00
-- url     : https://prove2.me/submissions/26378b04-4502-4e2f-b7ac-72cf42850377

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 9 34 degreeUnionState43_602 [34] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
