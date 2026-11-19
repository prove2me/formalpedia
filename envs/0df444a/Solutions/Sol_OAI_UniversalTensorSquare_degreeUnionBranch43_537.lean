-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_537
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:13.728417+00:00
-- url     : https://prove2.me/submissions/95c758ed-225f-4cc5-8bc0-5e318596a521

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 39 4 degreeUnionState43_537 [4] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
