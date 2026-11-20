-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1293
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:08:05.412179+00:00
-- url     : https://prove2.me/submissions/a723d629-0705-47bf-a6cd-af266169c0a9

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

lemma degreeUnionBranch62_1293_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 20 9 degreeUnionState62_1293 [9,9,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1293_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1293_oai
