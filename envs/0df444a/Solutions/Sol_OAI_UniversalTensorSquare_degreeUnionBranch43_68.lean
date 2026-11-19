-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_68
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:33:51.696925+00:00
-- url     : https://prove2.me/submissions/746557d3-3790-4644-ba03-10c99e23c591

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 24 4 degreeUnionState43_68 [4,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
