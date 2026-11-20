-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_245
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:14:30.903119+00:00
-- url     : https://prove2.me/submissions/f170171c-43fa-4c49-a289-7d3173dc292a

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

lemma degreeUnionBranch62_245_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 25 5 degreeUnionState62_245 [5,8,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_245_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_245_oai
