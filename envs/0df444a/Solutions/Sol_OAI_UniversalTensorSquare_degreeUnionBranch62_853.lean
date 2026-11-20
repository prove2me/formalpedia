-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_853
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:56:03.266571+00:00
-- url     : https://prove2.me/submissions/d4bc26af-77ce-4b8f-8aea-f921afbb21cb

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

lemma degreeUnionBranch62_853_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 24 8 degreeUnionState62_853 [8,8,8,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_853_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_853_oai
