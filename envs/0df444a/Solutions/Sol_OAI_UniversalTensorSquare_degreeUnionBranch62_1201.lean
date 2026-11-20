-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1201
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:26:28.430295+00:00
-- url     : https://prove2.me/submissions/4b6c8a25-b3d3-490d-aa94-5424f042e94b

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

lemma degreeUnionBranch62_1201_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 25 4 degreeUnionState62_1201 [4,9,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1201_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1201_oai
