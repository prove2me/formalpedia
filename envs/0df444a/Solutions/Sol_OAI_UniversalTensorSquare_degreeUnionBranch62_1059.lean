-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1059
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T05:14:22.737814+00:00
-- url     : https://prove2.me/submissions/13e09ec0-76b0-4ae9-9cb1-3fd918d486e6

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 30 10 degreeUnionState62_1059 [10,10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
