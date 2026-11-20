-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1222
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:39:20.651157+00:00
-- url     : https://prove2.me/submissions/ecc8104e-d225-4daf-969b-cd68a49ca280

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

lemma degreeUnionBranch62_1222_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 27 10 degreeUnionState62_1222 [10,12,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1222_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1222_oai
