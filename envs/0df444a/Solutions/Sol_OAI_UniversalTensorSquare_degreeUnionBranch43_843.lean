-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_843
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:42:42.989446+00:00
-- url     : https://prove2.me/submissions/1a43402b-6341-409e-aad7-c3efa9f00dca

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 11 32 degreeUnionState43_843 [32] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
