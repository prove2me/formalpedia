-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_49
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:58.068405+00:00
-- url     : https://prove2.me/submissions/f8b87e58-d7f4-4729-8a27-a4a8465a655c

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 23 7 degreeUnionState43_49 [7,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
