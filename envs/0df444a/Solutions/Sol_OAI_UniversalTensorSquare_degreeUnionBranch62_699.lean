-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_699
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:49:06.654326+00:00
-- url     : https://prove2.me/submissions/66961c48-59e2-4957-85f8-a9e922ccbb84

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

lemma degreeUnionBranch62_699_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 24 5 degreeUnionState62_699 [5,9,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_699_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_699_oai
