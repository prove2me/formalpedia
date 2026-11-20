-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1207
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:31:10.965908+00:00
-- url     : https://prove2.me/submissions/336e7b38-bee5-48a0-baa6-904f360761c5

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

lemma degreeUnionBranch62_1207_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 28 10 degreeUnionState62_1207 [10,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1207_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1207_oai
