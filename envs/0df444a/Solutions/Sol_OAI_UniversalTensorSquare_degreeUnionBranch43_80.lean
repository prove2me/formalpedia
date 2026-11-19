-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_80
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:42:53.918835+00:00
-- url     : https://prove2.me/submissions/3cdd2e10-f925-437a-85c4-8a04c41d904e

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 27 16 degreeUnionState43_80 [16] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
