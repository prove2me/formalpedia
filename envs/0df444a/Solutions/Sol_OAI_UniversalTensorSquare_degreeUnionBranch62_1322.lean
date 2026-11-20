-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1322
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:25:49.878486+00:00
-- url     : https://prove2.me/submissions/d27aa34d-4899-4eef-8fa4-a13773b7901f

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

lemma degreeUnionBranch62_1322_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 34 14 degreeUnionState62_1322 [14,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1322_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1322_oai
