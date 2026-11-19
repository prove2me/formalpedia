-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_587
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:07:53.952391+00:00
-- url     : https://prove2.me/submissions/b6381de9-6af7-4538-afc5-06013eb7328f

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 24 19 degreeUnionState43_587 [19] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
