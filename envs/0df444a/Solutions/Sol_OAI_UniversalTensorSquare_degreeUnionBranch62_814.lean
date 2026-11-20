-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_814
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:29:22.602188+00:00
-- url     : https://prove2.me/submissions/74d5941d-3cf2-4108-8d55-e7c1a1a03373

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

lemma degreeUnionBranch62_814_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 25 4 degreeUnionState62_814 [4,8,12,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_814_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_814_oai
