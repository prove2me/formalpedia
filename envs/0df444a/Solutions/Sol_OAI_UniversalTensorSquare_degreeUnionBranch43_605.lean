-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_605
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:39.922915+00:00
-- url     : https://prove2.me/submissions/ca24a9ea-8a9c-4fba-98b5-0b6dd8ee1aef

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 6 37 degreeUnionState43_605 [37] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
