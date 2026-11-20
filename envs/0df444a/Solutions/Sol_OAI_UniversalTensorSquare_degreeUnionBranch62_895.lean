-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_895
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:19:32.332412+00:00
-- url     : https://prove2.me/submissions/dcc9f015-ed6a-4a75-be6a-4e1cc79c275e

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

lemma degreeUnionBranch62_895_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 25 4 degreeUnionState62_895 [4,9,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_895_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_895_oai
