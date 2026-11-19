-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_110
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:37:11.903248+00:00
-- url     : https://prove2.me/submissions/a71fe87e-7f35-45b7-ae6d-bc11084720c2

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 58. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_110_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 13 45 13 degreeUnionState58_110 [13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_110_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_110_oai
