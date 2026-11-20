-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_411
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:52:29.426065+00:00
-- url     : https://prove2.me/submissions/ea27ef28-4dc4-4315-95be-52e9f0a9d9a0

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

lemma degreeUnionBranch62_411_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 28 5 degreeUnionState62_411 [5,7,8,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_411_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_411_oai
