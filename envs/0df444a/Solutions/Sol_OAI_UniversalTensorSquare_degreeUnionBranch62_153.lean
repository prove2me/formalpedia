-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_153
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:30:25.048179+00:00
-- url     : https://prove2.me/submissions/a65f11a7-afcc-49eb-9dde-b0447932a1ea

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

lemma degreeUnionBranch62_153_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 36 5 degreeUnionState62_153 [5,9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_153_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_153_oai
