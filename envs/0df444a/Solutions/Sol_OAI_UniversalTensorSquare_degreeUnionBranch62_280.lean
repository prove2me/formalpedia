-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_280
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:35:16.093512+00:00
-- url     : https://prove2.me/submissions/9cbe604e-7d9d-4a27-8ac2-2ff32b94f728

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

lemma degreeUnionBranch62_280_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 28 5 degreeUnionState62_280 [5,8,8,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_280_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_280_oai
