-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_455
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:21:29.36628+00:00
-- url     : https://prove2.me/submissions/c1e242d4-6518-45ec-ab8a-84636dae3682

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

lemma degreeUnionBranch62_455_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 23 7 degreeUnionState62_455 [7,8,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_455_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_455_oai
