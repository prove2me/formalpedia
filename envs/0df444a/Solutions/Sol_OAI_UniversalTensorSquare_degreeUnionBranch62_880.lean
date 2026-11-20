-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_880
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:08:20.111411+00:00
-- url     : https://prove2.me/submissions/8d671992-672f-4394-857a-f6b328da8ca4

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

lemma degreeUnionBranch62_880_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 32 6 degreeUnionState62_880 [6,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_880_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_880_oai
