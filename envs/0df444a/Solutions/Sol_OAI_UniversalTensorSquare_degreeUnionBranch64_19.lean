-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch64_19
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:49:38.658257+00:00
-- url     : https://prove2.me/submissions/345be100-e6e0-4b2c-bb7b-886bfb14bde3

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 14 degreeQs64 degreeTree64) 19 64 30 degreeHalfRegions64 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
