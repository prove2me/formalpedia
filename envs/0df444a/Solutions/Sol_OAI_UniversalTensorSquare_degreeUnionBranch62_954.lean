-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_954
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:54:33.840693+00:00
-- url     : https://prove2.me/submissions/f630e678-0d2f-4291-ba98-53ee94705c80

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 52 10 degreeUnionState62_954 [10] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
