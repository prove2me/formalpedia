-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1297
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:11:47.248956+00:00
-- url     : https://prove2.me/submissions/cad48d74-a839-46d5-8845-d6228e0d0eb1

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

lemma degreeUnionBranch62_1297_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 32 5 degreeUnionState62_1297 [5,11,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1297_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1297_oai
