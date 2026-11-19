-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_922
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:54:35.684709+00:00
-- url     : https://prove2.me/submissions/52430589-a578-4e38-ab7d-8dea522cb96e

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

theorem _root_.solution : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 36 12 degreeUnionState62_922 [12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end
