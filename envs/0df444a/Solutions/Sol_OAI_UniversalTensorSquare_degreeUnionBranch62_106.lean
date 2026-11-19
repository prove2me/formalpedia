-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_106
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:15:04.403393+00:00
-- url     : https://prove2.me/submissions/6547e892-fca9-46df-bf2e-b784759f4721

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

lemma degreeUnionBranch62_106_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 21 10 degreeUnionState62_106 [10,10,10,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_106_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_106_oai
