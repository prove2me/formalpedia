-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_760
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:06:45.260721+00:00
-- url     : https://prove2.me/submissions/fcdd5597-1733-40fd-8b25-fe348e6c155f

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 62. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_760_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 27 3 degreeUnionState62_760 [3,9,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_760_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_760_oai
