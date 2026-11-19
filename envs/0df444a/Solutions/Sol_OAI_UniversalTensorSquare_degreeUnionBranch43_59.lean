-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_59
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:53.042636+00:00
-- url     : https://prove2.me/submissions/29ecde9d-e41f-44af-be53-837f68f9bb87

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 22 7 degreeUnionState43_59 [7,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
