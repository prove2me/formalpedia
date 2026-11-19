-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_195
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T05:12:25.926494+00:00
-- url     : https://prove2.me/submissions/f395902b-22f7-4daa-af9b-c74b42b1ae8d

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 30 10 degreeUnionState62_195 [10,10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
