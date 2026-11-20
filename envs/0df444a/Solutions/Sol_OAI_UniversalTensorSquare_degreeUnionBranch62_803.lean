-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_803
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:29:09.305981+00:00
-- url     : https://prove2.me/submissions/83a9d8e1-d08e-40f9-b5c3-c9d70939e190

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

lemma degreeUnionBranch62_803_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 33 4 degreeUnionState62_803 [4,12,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_803_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_803_oai
