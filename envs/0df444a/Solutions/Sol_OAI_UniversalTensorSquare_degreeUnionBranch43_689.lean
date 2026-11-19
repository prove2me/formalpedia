-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_689
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:33:45.662456+00:00
-- url     : https://prove2.me/submissions/634a722c-b87f-465b-a25d-3c5a7f18d498

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 35 8 degreeUnionState43_689 [8] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
