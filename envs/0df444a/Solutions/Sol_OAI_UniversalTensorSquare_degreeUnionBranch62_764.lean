-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_764
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:07:12.618251+00:00
-- url     : https://prove2.me/submissions/6d6d0eb5-7260-4414-859f-1c8edc8d1b6b

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

lemma degreeUnionBranch62_764_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 23 7 degreeUnionState62_764 [7,9,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_764_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_764_oai
