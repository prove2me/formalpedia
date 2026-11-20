-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_917
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:25:20.988505+00:00
-- url     : https://prove2.me/submissions/24c0c8e0-1aeb-4f8b-b409-e81f5e5c4c6c

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

lemma degreeUnionBranch62_917_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 22 7 degreeUnionState62_917 [7,8,11,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_917_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_917_oai
