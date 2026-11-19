-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_840
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:10:23.359335+00:00
-- url     : https://prove2.me/submissions/4758aa9b-3e35-4993-b58d-1f366077d77a

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 14 29 degreeUnionState43_840 [29] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
