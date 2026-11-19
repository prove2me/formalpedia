-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_111
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:41:33.643782+00:00
-- url     : https://prove2.me/submissions/49962e08-fa5d-47c1-b0b9-2e15a03159c9

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

lemma degreeUnionBranch58_111_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 13 44 14 degreeUnionState58_111 [14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_111_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_111_oai
