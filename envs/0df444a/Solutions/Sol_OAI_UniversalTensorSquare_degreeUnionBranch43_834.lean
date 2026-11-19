-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_834
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:42:47.271075+00:00
-- url     : https://prove2.me/submissions/a41dd70d-6abf-44aa-bc91-b8bde6ad2e5f

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 20 23 degreeUnionState43_834 [23] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
