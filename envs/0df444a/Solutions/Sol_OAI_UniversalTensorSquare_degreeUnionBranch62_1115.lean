-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1115
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:49:09.703331+00:00
-- url     : https://prove2.me/submissions/1f62b32f-46e4-4e84-bba0-0bcfc785f807

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

lemma degreeUnionBranch62_1115_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 22 7 degreeUnionState62_1115 [7,9,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1115_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1115_oai
