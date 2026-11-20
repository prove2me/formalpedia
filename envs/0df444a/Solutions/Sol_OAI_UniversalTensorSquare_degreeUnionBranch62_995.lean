-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_995
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:55:06.520002+00:00
-- url     : https://prove2.me/submissions/0b265dea-9ace-4433-a7e1-d8f5074223ad

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

lemma degreeUnionBranch62_995_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 25 4 degreeUnionState62_995 [4,11,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_995_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_995_oai
