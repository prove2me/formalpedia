-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1190
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:26:09.867655+00:00
-- url     : https://prove2.me/submissions/5a89b3f5-14b3-4b75-8580-7677023083d9

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

lemma degreeUnionBranch62_1190_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 32 6 degreeUnionState62_1190 [6,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1190_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1190_oai
