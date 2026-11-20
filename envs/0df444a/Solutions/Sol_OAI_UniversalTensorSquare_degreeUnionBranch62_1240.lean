-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:46:50.019376+00:00
-- url     : https://prove2.me/submissions/f93ed53a-97a7-46eb-9244-eb6168bb1edf

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

lemma degreeUnionBranch62_1240_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 42 6 degreeUnionState62_1240 [6,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1240_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1240_oai
