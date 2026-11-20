-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_402
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:48:00.146158+00:00
-- url     : https://prove2.me/submissions/cdcb9c67-2562-4992-a825-0da725f3d215

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

lemma degreeUnionBranch62_402_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 29 5 degreeUnionState62_402 [5,7,7,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_402_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_402_oai
