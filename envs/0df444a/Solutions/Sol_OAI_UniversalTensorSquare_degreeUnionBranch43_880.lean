-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_880
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:42.650476+00:00
-- url     : https://prove2.me/submissions/f0a818a7-5221-441b-95e1-e2b2a9e2c2fe

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 16 15 28 degreeUnionState43_880 [28] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
