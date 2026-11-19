-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch64_22
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:49:30.195089+00:00
-- url     : https://prove2.me/submissions/39bda104-a048-4b99-bc06-a466dcacfd7c

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 14 degreeQs64 degreeTree64) 22 64 30 degreeHalfRegions64 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
