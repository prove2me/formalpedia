-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_670
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T04:05:32.158724+00:00
-- url     : https://prove2.me/submissions/97d495a1-d365-499d-bfa9-248570a7430f

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 29 10 degreeUnionState62_670 [10,11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
