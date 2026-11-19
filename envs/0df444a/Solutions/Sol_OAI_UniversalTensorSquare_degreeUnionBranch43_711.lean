-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_711
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:33:32.879493+00:00
-- url     : https://prove2.me/submissions/b3c185f5-8e1c-48b0-ad72-a660e2fe1f7c

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 21 22 degreeUnionState43_711 [22] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
