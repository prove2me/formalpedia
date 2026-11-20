-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_603
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:05:30.817169+00:00
-- url     : https://prove2.me/submissions/e85e4a43-b178-4c2b-a0ce-f944f43a9fb9

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

lemma degreeUnionBranch62_603_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 37 4 degreeUnionState62_603 [4,9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_603_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_603_oai
