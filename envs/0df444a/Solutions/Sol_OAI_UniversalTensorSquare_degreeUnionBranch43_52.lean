-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_52
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:25.921529+00:00
-- url     : https://prove2.me/submissions/6c6ce24f-17e3-4d39-9737-90aa84f4362f

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 20 10 degreeUnionState43_52 [10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
