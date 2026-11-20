-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_615
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:11:21.436655+00:00
-- url     : https://prove2.me/submissions/704985ae-f9f6-4a15-8204-c217e573a2af

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

lemma degreeUnionBranch62_615_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 27 5 degreeUnionState62_615 [5,9,9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_615_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_615_oai
