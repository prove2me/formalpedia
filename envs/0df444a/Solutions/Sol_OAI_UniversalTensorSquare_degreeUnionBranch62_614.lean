-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_614
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:11:14.663125+00:00
-- url     : https://prove2.me/submissions/0f46f6ae-a14b-424b-a1a0-3b27bcef6054

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

lemma degreeUnionBranch62_614_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 28 4 degreeUnionState62_614 [4,9,9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_614_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_614_oai
