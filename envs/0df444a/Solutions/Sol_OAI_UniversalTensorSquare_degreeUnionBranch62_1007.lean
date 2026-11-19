-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1007
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:05:33.190565+00:00
-- url     : https://prove2.me/submissions/c5fe2aea-1a94-4ecb-96fe-c6732784aedf

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

lemma degreeUnionBranch62_1007_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 43 7 degreeUnionState62_1007 [7,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1007_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1007_oai
