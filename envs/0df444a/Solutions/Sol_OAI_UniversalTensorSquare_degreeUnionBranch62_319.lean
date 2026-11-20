-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_319
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:58:35.267183+00:00
-- url     : https://prove2.me/submissions/f2a4ac6f-f949-4ab5-b2ea-a049b19edfa6

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

lemma degreeUnionBranch62_319_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 24 7 degreeUnionState62_319 [7,8,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_319_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_319_oai
