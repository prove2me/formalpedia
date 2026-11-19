-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch43_900
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T04:37:04.836203+00:00
-- url     : https://prove2.me/submissions/5f17badd-c5a3-4380-8752-74446fb07861

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 23 43 42 degreeHalfRegions43 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
