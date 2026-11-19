-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_483
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T05:15:06.257209+00:00
-- url     : https://prove2.me/submissions/b420cac8-8318-4302-85ec-f0f8db6cecb0

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 36 12 degreeUnionState62_483 [12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
