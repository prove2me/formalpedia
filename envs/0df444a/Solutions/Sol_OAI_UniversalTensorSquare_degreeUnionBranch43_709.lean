-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_709
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:33:29.822347+00:00
-- url     : https://prove2.me/submissions/b853abfb-358a-4257-ae9b-31f250ffc94f

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 23 20 degreeUnionState43_709 [20] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
