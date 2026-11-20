-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_235
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:10:33.48701+00:00
-- url     : https://prove2.me/submissions/a428b568-66e0-45e0-b617-27be041ce0fb

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

lemma degreeUnionBranch62_235_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 34 4 degreeUnionState62_235 [4,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_235_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_235_oai
