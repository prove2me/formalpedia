-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_57
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:58.746619+00:00
-- url     : https://prove2.me/submissions/b00ec1a8-1cf5-4d18-93fd-bd0ae7c284bb

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 24 5 degreeUnionState43_57 [5,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
