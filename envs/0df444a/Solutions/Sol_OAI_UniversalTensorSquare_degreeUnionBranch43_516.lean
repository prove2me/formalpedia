-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_516
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:48.032447+00:00
-- url     : https://prove2.me/submissions/cad4a8f8-6c51-46e5-ae92-3dd0d48c9237

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 20 23 degreeUnionState43_516 [23] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
