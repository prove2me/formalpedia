-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_753
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:43:01.234215+00:00
-- url     : https://prove2.me/submissions/9c2819e5-e8bc-464b-907b-0dd25d3099a2

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 19 24 degreeUnionState43_753 [24] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
