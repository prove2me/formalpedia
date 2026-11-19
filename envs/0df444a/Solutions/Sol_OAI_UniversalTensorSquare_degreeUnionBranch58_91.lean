-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_91
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:51:25.115581+00:00
-- url     : https://prove2.me/submissions/6649b6b3-bbdf-4fb9-9398-d566486ff4e8

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

lemma degreeUnionBranch58_91_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 44 14 degreeUnionState58_91 [14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_91_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_91_oai
