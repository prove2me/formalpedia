-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_464
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:21:50.45372+00:00
-- url     : https://prove2.me/submissions/19c52bc7-2469-42c5-acb3-9a6eef01c4df

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

lemma degreeUnionBranch62_464_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 28 10 degreeUnionState62_464 [10,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_464_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_464_oai
