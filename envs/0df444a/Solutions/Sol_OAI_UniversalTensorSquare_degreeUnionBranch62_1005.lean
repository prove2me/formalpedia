-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1005
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:57:29.078195+00:00
-- url     : https://prove2.me/submissions/a98a5e1e-4163-46da-9ae4-d6db1b0f8278

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

lemma degreeUnionBranch62_1005_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 45 5 degreeUnionState62_1005 [5,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1005_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1005_oai
