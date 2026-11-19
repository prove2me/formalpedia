-- Prove2me | solution 2 for OAI.UniversalTensorSquare.degreeUnionBranch43_830
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T04:23:27.443769+00:00
-- url     : https://prove2.me/submissions/f0ec2902-3f9f-4e8a-a06c-a7d4a87b4dfa

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 24 19 degreeUnionState43_830 [19] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
