-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_775
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:18:05.732276+00:00
-- url     : https://prove2.me/submissions/e81b1c34-5443-44fa-b0ea-8c77ad869975

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

lemma degreeUnionBranch62_775_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 19 10 degreeUnionState62_775 [10,10,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_775_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_775_oai
