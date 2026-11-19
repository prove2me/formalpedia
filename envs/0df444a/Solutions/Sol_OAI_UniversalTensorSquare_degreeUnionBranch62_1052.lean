-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1052
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:18:27.970191+00:00
-- url     : https://prove2.me/submissions/a73a648e-1807-4d4b-83e2-9caa50e7c1d4

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

lemma degreeUnionBranch62_1052_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 28 3 degreeUnionState62_1052 [3,9,10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1052_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1052_oai
