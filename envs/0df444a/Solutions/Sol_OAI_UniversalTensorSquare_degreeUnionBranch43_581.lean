-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_581
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:05.356124+00:00
-- url     : https://prove2.me/submissions/9d082494-dcad-482f-9170-b21aacfe5361

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 30 13 degreeUnionState43_581 [13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
