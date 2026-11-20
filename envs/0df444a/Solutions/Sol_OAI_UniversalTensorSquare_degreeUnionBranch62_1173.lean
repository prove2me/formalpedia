-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1173
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:21:46.096848+00:00
-- url     : https://prove2.me/submissions/14277ac3-5581-49ca-990b-d122ed3932ca

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

lemma degreeUnionBranch62_1173_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 25 5 degreeUnionState62_1173 [5,9,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1173_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1173_oai
