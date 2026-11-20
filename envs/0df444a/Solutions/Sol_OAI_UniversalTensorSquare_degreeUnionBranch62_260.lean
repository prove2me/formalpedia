-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_260
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:26:19.857917+00:00
-- url     : https://prove2.me/submissions/6c6039e7-de3e-429b-976e-13eb608efa1a

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

lemma degreeUnionBranch62_260_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 44 5 degreeUnionState62_260 [5,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_260_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_260_oai
