-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_993
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T04:02:07.605864+00:00
-- url     : https://prove2.me/submissions/d90e18cc-5947-4591-9969-c13441677cae

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 29 11 degreeUnionState62_993 [11,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
