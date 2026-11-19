-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_839
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:42:46.169421+00:00
-- url     : https://prove2.me/submissions/d0f6983f-a565-4f70-87f8-0ced8ce788c4

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 15 28 degreeUnionState43_839 [28] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
