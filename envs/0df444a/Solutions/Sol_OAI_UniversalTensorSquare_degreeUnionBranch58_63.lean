-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_63
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:50:55.009291+00:00
-- url     : https://prove2.me/submissions/b570dd58-8e16-45d0-9bee-2cca6050574e

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

lemma degreeUnionBranch58_63_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 53 5 degreeUnionState58_63 [5] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_63_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_63_oai
