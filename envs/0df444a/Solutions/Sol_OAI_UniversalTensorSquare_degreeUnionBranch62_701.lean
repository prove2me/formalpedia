-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_701
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:44:08.888747+00:00
-- url     : https://prove2.me/submissions/85075574-e0d5-4589-bb82-6769e535d738

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

lemma degreeUnionBranch62_701_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 22 7 degreeUnionState62_701 [7,9,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_701_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_701_oai
