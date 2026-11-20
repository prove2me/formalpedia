-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_421
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:57:26.608717+00:00
-- url     : https://prove2.me/submissions/5c0fc36d-87fd-477c-94c4-ffb847ea597c

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

lemma degreeUnionBranch62_421_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 35 4 degreeUnionState62_421 [4,9,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_421_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_421_oai
