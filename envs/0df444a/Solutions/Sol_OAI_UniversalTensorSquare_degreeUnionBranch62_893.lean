-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_893
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T04:02:08.577188+00:00
-- url     : https://prove2.me/submissions/c4cf806c-82e2-4e80-8555-4e1af3b4e755

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 29 9 degreeUnionState62_893 [9,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
