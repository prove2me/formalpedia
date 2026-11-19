-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_754
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:37:28.847711+00:00
-- url     : https://prove2.me/submissions/1457074d-2dbf-4e16-94bc-3199f8a5da2e

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 18 25 degreeUnionState43_754 [25] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
