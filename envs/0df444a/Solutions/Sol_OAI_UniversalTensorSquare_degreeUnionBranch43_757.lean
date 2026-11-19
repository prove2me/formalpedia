-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_757
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:37:26.884762+00:00
-- url     : https://prove2.me/submissions/1e7a63ac-1a50-49c5-a3a0-0617093cc3cd

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 15 28 degreeUnionState43_757 [28] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
