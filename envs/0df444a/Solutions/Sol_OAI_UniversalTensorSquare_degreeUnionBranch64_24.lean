-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch64_24
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:49:34.389053+00:00
-- url     : https://prove2.me/submissions/47fa46e9-5122-4f24-bcfc-667b27ceb987

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 14 degreeQs64 degreeTree64) 24 64 30 degreeHalfRegions64 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
