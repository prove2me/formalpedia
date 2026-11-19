-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_896
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T04:33:54.933205+00:00
-- url     : https://prove2.me/submissions/526d09e4-6464-4210-978d-a24782cf535f

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 19 43 42 degreeHalfRegions43 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
