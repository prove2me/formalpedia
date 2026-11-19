-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch43_431
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:16.544927+00:00
-- url     : https://prove2.me/submissions/8fee303e-b418-4d16-8dc9-e92e6da3d51e

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 17 12 degreeUnionState43_431 [12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
