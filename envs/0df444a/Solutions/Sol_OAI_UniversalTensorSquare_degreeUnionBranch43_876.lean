-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_876
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:43.572981+00:00
-- url     : https://prove2.me/submissions/cde3ad05-a21f-4ac0-8997-84006f278ad7

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 16 19 24 degreeUnionState43_876 [24] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
