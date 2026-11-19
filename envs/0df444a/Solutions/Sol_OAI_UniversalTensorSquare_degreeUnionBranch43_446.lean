-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_446
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:09.288645+00:00
-- url     : https://prove2.me/submissions/4848d8e5-cb50-4da7-b923-027f93e3ba68

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 13 15 degreeUnionState43_446 [15,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
