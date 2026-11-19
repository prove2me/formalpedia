-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_47
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:50.972085+00:00
-- url     : https://prove2.me/submissions/f307efdd-19b3-4905-8c22-d07aa42cda8c

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 25 5 degreeUnionState43_47 [5,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
