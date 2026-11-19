-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_588
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:54.929213+00:00
-- url     : https://prove2.me/submissions/5aa7f797-327d-444c-afa7-708e34aafe9e

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 23 20 degreeUnionState43_588 [20] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
