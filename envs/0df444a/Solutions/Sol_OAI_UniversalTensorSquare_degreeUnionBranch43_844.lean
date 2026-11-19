-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_844
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:10:22.402863+00:00
-- url     : https://prove2.me/submissions/d1d99436-316c-4013-96f7-be8be64380a3

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 10 33 degreeUnionState43_844 [33] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
