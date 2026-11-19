-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch43_44
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:09:14.739015+00:00
-- url     : https://prove2.me/submissions/85ededd8-0e13-4283-95f0-2881f79fcad8

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 20 11 degreeUnionState43_44 [11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
