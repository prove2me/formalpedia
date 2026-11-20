-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_891
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:19:05.598977+00:00
-- url     : https://prove2.me/submissions/5a165dff-206f-46f9-8af4-2bc8f380235e

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

lemma degreeUnionBranch62_891_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 23 7 degreeUnionState62_891 [7,8,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_891_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_891_oai
