-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_612
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:35.492307+00:00
-- url     : https://prove2.me/submissions/72e482f9-3023-483a-9e2b-8ac7a5259d67

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 39 4 degreeUnionState43_612 [4] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
