-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_460
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:27:26.082246+00:00
-- url     : https://prove2.me/submissions/d7eee6ef-9533-46b3-a330-9fca31df9fd7

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

lemma degreeUnionBranch62_460_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 23 6 degreeUnionState62_460 [6,9,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_460_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_460_oai
