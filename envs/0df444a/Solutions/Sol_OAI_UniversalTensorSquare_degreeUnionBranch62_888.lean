-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_888
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:08:47.683898+00:00
-- url     : https://prove2.me/submissions/4383d821-4756-44bd-83f4-14859ea3bb36

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

lemma degreeUnionBranch62_888_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 26 4 degreeUnionState62_888 [4,8,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_888_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_888_oai
