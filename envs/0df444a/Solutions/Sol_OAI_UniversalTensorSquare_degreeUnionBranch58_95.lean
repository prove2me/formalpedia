-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_95
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:56:35.057324+00:00
-- url     : https://prove2.me/submissions/f803bc97-e877-4792-9e03-2d8a9d4745a4

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

lemma degreeUnionBranch58_95_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 13 51 7 degreeUnionState58_95 [7] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_95_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_95_oai
