-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_971
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:48:46.002994+00:00
-- url     : https://prove2.me/submissions/b519d25a-14d3-4377-8b68-85af21d2a4d7

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

lemma degreeUnionBranch62_971_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 36 5 degreeUnionState62_971 [5,10,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_971_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_971_oai
