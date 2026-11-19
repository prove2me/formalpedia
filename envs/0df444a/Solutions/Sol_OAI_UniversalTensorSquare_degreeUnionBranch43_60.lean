-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_60
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:41.818713+00:00
-- url     : https://prove2.me/submissions/4fcae18f-cf8f-4a89-8272-bf2d56e44148

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 21 8 degreeUnionState43_60 [8,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
