-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_592
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:49.854871+00:00
-- url     : https://prove2.me/submissions/af1a529a-dad9-468f-8699-ab0fa2d6b8bc

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 19 24 degreeUnionState43_592 [24] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
