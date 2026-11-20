-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_43
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:00:34.795327+00:00
-- url     : https://prove2.me/submissions/735e7e93-7446-48df-a360-90d85cc4a605

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

lemma degreeUnionBranch62_43_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 38 10 degreeUnionState62_43 [10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_43_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_43_oai
