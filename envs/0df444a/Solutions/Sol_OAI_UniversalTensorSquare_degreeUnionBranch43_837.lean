-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_837
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:10:26.37503+00:00
-- url     : https://prove2.me/submissions/bc1a739d-735f-47ad-84e6-5ea2d5f7bdd1

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 17 26 degreeUnionState43_837 [26] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
