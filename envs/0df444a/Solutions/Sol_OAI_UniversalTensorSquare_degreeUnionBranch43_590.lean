-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_590
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:55.83968+00:00
-- url     : https://prove2.me/submissions/14078af7-238f-475c-9383-db3b086a2bc8

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 21 22 degreeUnionState43_590 [22] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
