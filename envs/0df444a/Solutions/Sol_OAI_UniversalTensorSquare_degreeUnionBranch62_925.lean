-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_925
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:31:52.226176+00:00
-- url     : https://prove2.me/submissions/9f61eaae-e75e-4627-baf2-79e15a4606a6

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

lemma degreeUnionBranch62_925_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 30 6 degreeUnionState62_925 [6,12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_925_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_925_oai
