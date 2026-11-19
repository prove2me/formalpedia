-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1089
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:32:38.636202+00:00
-- url     : https://prove2.me/submissions/06618199-d9d4-49c5-b634-d9345c845e08

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

lemma degreeUnionBranch62_1089_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 26 3 degreeUnionState62_1089 [3,10,11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1089_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1089_oai
