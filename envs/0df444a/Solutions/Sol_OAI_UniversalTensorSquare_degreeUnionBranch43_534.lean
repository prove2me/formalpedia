-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_534
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:10.053627+00:00
-- url     : https://prove2.me/submissions/a518b17e-6531-4af8-8bab-2890cb9c06dd

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 2 41 degreeUnionState43_534 [41] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
