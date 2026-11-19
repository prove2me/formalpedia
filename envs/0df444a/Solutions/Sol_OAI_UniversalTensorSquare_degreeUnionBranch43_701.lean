-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_701
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:33:40.157951+00:00
-- url     : https://prove2.me/submissions/f7c407f0-a546-4214-bf3c-c8932c5b47b6

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 31 12 degreeUnionState43_701 [12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
