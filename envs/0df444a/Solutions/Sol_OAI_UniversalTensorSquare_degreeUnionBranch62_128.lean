-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_128
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:59:01.046787+00:00
-- url     : https://prove2.me/submissions/3ae2f0dd-f296-402a-a9c2-05e00a27a726

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

lemma degreeUnionBranch62_128_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 20 9 degreeUnionState62_128 [9,11,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_128_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_128_oai
