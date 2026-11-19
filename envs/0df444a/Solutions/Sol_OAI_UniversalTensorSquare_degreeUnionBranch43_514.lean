-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_514
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:08:58.984804+00:00
-- url     : https://prove2.me/submissions/8173f8dc-f88a-41af-9a60-dd9eb8372702

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 22 21 degreeUnionState43_514 [21] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
