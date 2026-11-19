-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_93
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:56:28.939207+00:00
-- url     : https://prove2.me/submissions/fa9f0feb-00a7-4715-b63e-65bc2f5739c3

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

lemma degreeUnionBranch58_93_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 13 53 5 degreeUnionState58_93 [5] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_93_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_93_oai
