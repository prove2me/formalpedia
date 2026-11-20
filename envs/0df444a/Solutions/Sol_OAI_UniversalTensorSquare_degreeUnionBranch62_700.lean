-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_700
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:49:13.503722+00:00
-- url     : https://prove2.me/submissions/96e3d711-b0df-490a-8419-e6102a857746

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

lemma degreeUnionBranch62_700_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 23 6 degreeUnionState62_700 [6,9,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_700_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_700_oai
