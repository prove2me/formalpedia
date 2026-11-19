-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_54
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:11.016231+00:00
-- url     : https://prove2.me/submissions/2e2ff79d-6999-41e1-abe1-387e3a7caa75

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 18 12 degreeUnionState43_54 [12,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
