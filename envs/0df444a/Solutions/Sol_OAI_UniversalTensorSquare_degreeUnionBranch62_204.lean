-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_204
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:56:29.225575+00:00
-- url     : https://prove2.me/submissions/edd6d040-b9f7-4227-9e75-db271f5e47f3

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

lemma degreeUnionBranch62_204_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 35 4 degreeUnionState62_204 [4,11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_204_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_204_oai
