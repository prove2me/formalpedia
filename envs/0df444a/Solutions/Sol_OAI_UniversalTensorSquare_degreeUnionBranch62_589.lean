-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_589
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:00:09.47621+00:00
-- url     : https://prove2.me/submissions/3b47589f-6440-4c37-a9b7-6d01fa43b6cf

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

lemma degreeUnionBranch62_589_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 44 6 degreeUnionState62_589 [6,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_589_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_589_oai
