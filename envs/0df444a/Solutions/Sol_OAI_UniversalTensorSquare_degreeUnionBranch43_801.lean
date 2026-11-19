-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_801
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:42:58.027414+00:00
-- url     : https://prove2.me/submissions/f2b0b0de-fd74-429b-af26-a3d375831d17

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 12 31 degreeUnionState43_801 [31] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
