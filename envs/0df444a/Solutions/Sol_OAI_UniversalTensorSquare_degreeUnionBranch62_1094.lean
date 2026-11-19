-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1094
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:37:53.962285+00:00
-- url     : https://prove2.me/submissions/acb64b1a-0cbd-4dc8-a599-f3e98419b24a

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

lemma degreeUnionBranch62_1094_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 21 8 degreeUnionState62_1094 [8,10,11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1094_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1094_oai
