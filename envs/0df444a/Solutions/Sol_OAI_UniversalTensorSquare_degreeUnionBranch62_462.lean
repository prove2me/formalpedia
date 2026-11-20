-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_462
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:21:43.175181+00:00
-- url     : https://prove2.me/submissions/83f99875-4885-4b4f-a0c0-7528be08b846

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

lemma degreeUnionBranch62_462_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 21 8 degreeUnionState62_462 [8,9,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_462_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_462_oai
