-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1133
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:03:06.093378+00:00
-- url     : https://prove2.me/submissions/657c66f2-8b05-4019-96f0-038ac133a57f

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

lemma degreeUnionBranch62_1133_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 29 4 degreeUnionState62_1133 [4,8,8,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1133_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1133_oai
