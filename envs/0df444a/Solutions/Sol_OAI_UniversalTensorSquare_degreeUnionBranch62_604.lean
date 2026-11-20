-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_604
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:10:54.398964+00:00
-- url     : https://prove2.me/submissions/6edbb15c-351b-4e75-b883-b4ab2736338b

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

lemma degreeUnionBranch62_604_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 36 5 degreeUnionState62_604 [5,9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_604_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_604_oai
