-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_745
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:06:12.138415+00:00
-- url     : https://prove2.me/submissions/dbd85245-ccd6-42c2-97c7-d9e36727f42a

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

lemma degreeUnionBranch62_745_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 35 4 degreeUnionState62_745 [4,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_745_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_745_oai
