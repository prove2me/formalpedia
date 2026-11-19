-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_20
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T04:39:34.01958+00:00
-- url     : https://prove2.me/submissions/ea8cb692-b23a-41db-9040-76ef3e9d0229

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 46 12 degreeUnionState58_20 [12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
