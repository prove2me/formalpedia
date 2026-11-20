-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1313
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:20:49.132884+00:00
-- url     : https://prove2.me/submissions/a828a9bd-4679-4657-a2ed-ba556d891bd3

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

lemma degreeUnionBranch62_1313_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 31 5 degreeUnionState62_1313 [5,12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1313_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1313_oai
