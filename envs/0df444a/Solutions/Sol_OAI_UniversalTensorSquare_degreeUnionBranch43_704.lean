-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_704
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:33:36.737745+00:00
-- url     : https://prove2.me/submissions/98ed4b26-f562-48cb-b2c5-696a698f79c7

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 28 15 degreeUnionState43_704 [15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
