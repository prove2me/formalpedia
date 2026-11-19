-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_795
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:43:00.19177+00:00
-- url     : https://prove2.me/submissions/04e3831a-8193-4066-888a-8a31aa78f310

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 18 25 degreeUnionState43_795 [25] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
