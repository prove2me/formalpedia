-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch58_25
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T04:43:45.219441+00:00
-- url     : https://prove2.me/submissions/0128e9e9-e555-499d-a909-4f49aa3a1726

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 37 9 degreeUnionState58_25 [9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
