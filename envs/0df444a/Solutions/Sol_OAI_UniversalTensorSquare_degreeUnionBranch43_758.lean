-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_758
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:37:23.893189+00:00
-- url     : https://prove2.me/submissions/eab9f370-d67c-4ba2-bfb4-a0ac129c0a62

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 14 29 degreeUnionState43_758 [29] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
