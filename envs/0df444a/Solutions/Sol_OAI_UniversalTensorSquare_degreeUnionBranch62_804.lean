-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_804
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:24:23.930183+00:00
-- url     : https://prove2.me/submissions/0ed45114-bd40-46a9-bd0c-6994f60b393d

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

lemma degreeUnionBranch62_804_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 32 5 degreeUnionState62_804 [5,12,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_804_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_804_oai
