-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_92
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:49:41.699543+00:00
-- url     : https://prove2.me/submissions/8d173144-77f7-4fdc-80a9-78a74f655f29

import Mathlib
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US022
section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniversalTensorSquare

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 14 58 14 degreeHalfRegions58 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
