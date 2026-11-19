-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1096
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:38:07.018317+00:00
-- url     : https://prove2.me/submissions/f614b411-eaac-45df-880b-3a7819001b1a

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

lemma degreeUnionBranch62_1096_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 19 10 degreeUnionState62_1096 [10,10,11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1096_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1096_oai
