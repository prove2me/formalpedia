-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1321
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:21:27.489583+00:00
-- url     : https://prove2.me/submissions/6a0757b3-3bb7-42a6-b61e-d3031d00866e

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

lemma degreeUnionBranch62_1321_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 35 13 degreeUnionState62_1321 [13,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1321_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1321_oai
