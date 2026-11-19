-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:57:20.619748+00:00
-- url     : https://prove2.me/submissions/80180ecf-2bbe-4e92-b349-69c7e947553c

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

lemma degreeUnionBranch62_10_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 62 28 degreeHalfRegions62 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_10_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_10_oai
