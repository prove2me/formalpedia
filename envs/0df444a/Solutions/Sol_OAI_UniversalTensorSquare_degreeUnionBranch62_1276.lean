-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1276
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:58:48.556556+00:00
-- url     : https://prove2.me/submissions/ed9503b3-6594-42fe-9ba6-bae7475bc301

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

lemma degreeUnionBranch62_1276_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 33 5 degreeUnionState62_1276 [5,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1276_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1276_oai
