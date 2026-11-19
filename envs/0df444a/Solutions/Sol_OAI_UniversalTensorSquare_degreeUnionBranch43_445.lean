-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_445
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:08.355227+00:00
-- url     : https://prove2.me/submissions/b8e6305c-7849-40c9-9d8d-7971cdce157e

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 14 14 degreeUnionState43_445 [14,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
