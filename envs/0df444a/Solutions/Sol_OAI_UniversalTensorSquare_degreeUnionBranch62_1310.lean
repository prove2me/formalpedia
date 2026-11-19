-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1310
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T05:15:59.5721+00:00
-- url     : https://prove2.me/submissions/4a53ac3f-dc78-4ec7-b028-590dea3a1afa

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 36 12 degreeUnionState62_1310 [12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
