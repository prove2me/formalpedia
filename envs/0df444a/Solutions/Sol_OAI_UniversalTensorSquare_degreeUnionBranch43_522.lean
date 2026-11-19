-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_522
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:25.054851+00:00
-- url     : https://prove2.me/submissions/37c528bc-51f5-4858-8657-bc80ccbde144

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 14 29 degreeUnionState43_522 [29] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
