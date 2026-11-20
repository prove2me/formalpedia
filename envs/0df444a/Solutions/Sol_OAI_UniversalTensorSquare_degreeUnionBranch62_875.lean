-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_875
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:02:42.103889+00:00
-- url     : https://prove2.me/submissions/3ead17dd-8360-4f74-a3a5-32e02e599a58

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

lemma degreeUnionBranch62_875_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 22 8 degreeUnionState62_875 [8,9,9,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_875_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_875_oai
