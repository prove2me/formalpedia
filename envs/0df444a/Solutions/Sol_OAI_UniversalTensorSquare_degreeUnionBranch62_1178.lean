-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1178
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T05:09:27.817996+00:00
-- url     : https://prove2.me/submissions/5f78fec0-cb76-4532-a651-2501ea2d1350

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 29 10 degreeUnionState62_1178 [10,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
