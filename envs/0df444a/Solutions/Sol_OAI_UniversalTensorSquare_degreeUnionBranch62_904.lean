-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_904
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:24:32.342454+00:00
-- url     : https://prove2.me/submissions/347f5637-cf4f-4340-b763-e5a4af806d02

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

lemma degreeUnionBranch62_904_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 32 5 degreeUnionState62_904 [5,11,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_904_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_904_oai
