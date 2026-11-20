-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_453
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:16:35.198278+00:00
-- url     : https://prove2.me/submissions/9a610abf-b4e7-4ee7-ab1b-11f57baae85d

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

lemma degreeUnionBranch62_453_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 25 5 degreeUnionState62_453 [5,8,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_453_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_453_oai
