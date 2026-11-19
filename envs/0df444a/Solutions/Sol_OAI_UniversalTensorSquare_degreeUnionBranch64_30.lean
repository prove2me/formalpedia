-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch64_30
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:49:24.001684+00:00
-- url     : https://prove2.me/submissions/421385f7-6885-4127-a375-3732354ad18b

import Mathlib
import Definitions.Def_OAIQ259US022
section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniversalTensorSquare

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 14 degreeQs64 degreeTree64) 30 64 30 degreeHalfRegions64 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
