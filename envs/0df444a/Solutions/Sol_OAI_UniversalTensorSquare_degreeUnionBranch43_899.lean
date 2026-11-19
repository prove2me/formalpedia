-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_899
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T04:33:31.482463+00:00
-- url     : https://prove2.me/submissions/d458b541-d31c-4d01-8ac5-4dbe6ab14400

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 22 43 42 degreeHalfRegions43 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
