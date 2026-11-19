-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_249
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T05:04:21.04171+00:00
-- url     : https://prove2.me/submissions/5f328d95-78fd-4321-b18f-50a0baf2e0cf

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 29 9 degreeUnionState62_249 [9,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
