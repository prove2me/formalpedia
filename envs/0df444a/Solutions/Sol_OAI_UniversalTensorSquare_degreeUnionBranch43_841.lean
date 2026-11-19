-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_841
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:42:45.078276+00:00
-- url     : https://prove2.me/submissions/5e7c33af-fdda-4802-9120-070666c2b922

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 13 30 degreeUnionState43_841 [30] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
