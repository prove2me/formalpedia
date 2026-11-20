-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_350
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:21:38.301256+00:00
-- url     : https://prove2.me/submissions/0b8d8297-fe2f-42d9-9298-aa06ca8a3746

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

lemma degreeUnionBranch62_350_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 22 8 degreeUnionState62_350 [8,8,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_350_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_350_oai
