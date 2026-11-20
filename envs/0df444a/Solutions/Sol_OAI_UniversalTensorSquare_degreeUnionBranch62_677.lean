-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_677
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:38:11.487725+00:00
-- url     : https://prove2.me/submissions/60c5d224-cbdb-418d-b5f6-6e1b02ac3244

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

lemma degreeUnionBranch62_677_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 20 9 degreeUnionState62_677 [9,10,11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_677_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_677_oai
