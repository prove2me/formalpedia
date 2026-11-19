-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_19
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T04:41:50.159231+00:00
-- url     : https://prove2.me/submissions/29b0a5ef-ece6-4de4-9ab3-69164c312c25

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 47 11 degreeUnionState58_19 [11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
