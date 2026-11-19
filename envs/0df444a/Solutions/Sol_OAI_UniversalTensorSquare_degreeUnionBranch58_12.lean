-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_12
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T04:27:24.999615+00:00
-- url     : https://prove2.me/submissions/17a09a75-b007-4a7f-a69f-5978b5792d67

import Mathlib
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US022
section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniversalTensorSquare

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 58 14 degreeHalfRegions58 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
