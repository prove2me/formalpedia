-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_706
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:33:31.880907+00:00
-- url     : https://prove2.me/submissions/4b49fbe0-139a-4e97-b776-d72850a80489

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 26 17 degreeUnionState43_706 [17] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
