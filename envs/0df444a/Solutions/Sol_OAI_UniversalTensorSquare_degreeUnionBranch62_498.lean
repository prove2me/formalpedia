-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_498
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:49:13.008175+00:00
-- url     : https://prove2.me/submissions/f2cffa1a-2683-46f8-8a37-5941655c7e5f

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

lemma degreeUnionBranch62_498_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 34 14 degreeUnionState62_498 [14,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_498_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_498_oai
