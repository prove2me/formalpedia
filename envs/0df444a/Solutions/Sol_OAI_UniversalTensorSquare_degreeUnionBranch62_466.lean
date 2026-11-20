-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_466
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:27:47.296193+00:00
-- url     : https://prove2.me/submissions/65467040-53ce-4bec-9815-e17542d28459

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

lemma degreeUnionBranch62_466_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 33 4 degreeUnionState62_466 [4,11,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_466_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_466_oai
