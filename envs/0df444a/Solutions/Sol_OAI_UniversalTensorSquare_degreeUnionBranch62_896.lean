-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_896
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:19:39.05784+00:00
-- url     : https://prove2.me/submissions/f63bf03e-129c-4678-ae5f-624be06556e3

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

lemma degreeUnionBranch62_896_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 24 5 degreeUnionState62_896 [5,9,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_896_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_896_oai
