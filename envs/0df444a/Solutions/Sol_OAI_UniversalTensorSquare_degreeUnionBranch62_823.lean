-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_823
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T04:02:09.696693+00:00
-- url     : https://prove2.me/submissions/2fff9e21-df78-40ac-a70b-29fb5cf0b417

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 36 13 degreeUnionState62_823 [13,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
