-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_803
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:42:48.145825+00:00
-- url     : https://prove2.me/submissions/d55c3419-0a99-4b66-88d4-fa48015278ed

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 10 33 degreeUnionState43_803 [33] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
