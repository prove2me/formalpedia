-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_708
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:33:35.769683+00:00
-- url     : https://prove2.me/submissions/604981eb-3761-4fdb-bcba-3cdac7cfa5da

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 24 19 degreeUnionState43_708 [19] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
