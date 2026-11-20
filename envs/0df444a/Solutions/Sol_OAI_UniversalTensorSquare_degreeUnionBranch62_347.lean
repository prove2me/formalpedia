-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_347
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:12:45.682319+00:00
-- url     : https://prove2.me/submissions/4590b48f-036d-4aeb-b363-38b68fe4d055

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

lemma degreeUnionBranch62_347_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 25 5 degreeUnionState62_347 [5,8,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_347_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_347_oai
