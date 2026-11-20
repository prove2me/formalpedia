-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_928
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:32:06.121938+00:00
-- url     : https://prove2.me/submissions/32fea861-c650-4c88-9ee8-d185e838e4c8

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

lemma degreeUnionBranch62_928_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 27 9 degreeUnionState62_928 [9,12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_928_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_928_oai
