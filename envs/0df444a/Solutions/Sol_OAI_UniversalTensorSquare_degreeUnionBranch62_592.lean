-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_592
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:00:16.113369+00:00
-- url     : https://prove2.me/submissions/c9d80a0e-a0aa-459b-a512-7d7337861ef4

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

lemma degreeUnionBranch62_592_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 38 4 degreeUnionState62_592 [4,8,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_592_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_592_oai
