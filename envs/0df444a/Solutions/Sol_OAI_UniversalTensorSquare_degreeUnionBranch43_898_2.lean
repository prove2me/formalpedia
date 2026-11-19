-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch43_898
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T04:34:07.976302+00:00
-- url     : https://prove2.me/submissions/8a847d6c-1499-46ab-8b7c-d7bb4f23c0e6

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 21 43 42 degreeHalfRegions43 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
