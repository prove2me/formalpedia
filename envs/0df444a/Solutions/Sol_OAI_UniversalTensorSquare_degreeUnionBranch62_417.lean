-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_417
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:56:59.41849+00:00
-- url     : https://prove2.me/submissions/c34e0144-98a2-46e5-a116-9a2a3dc68fb1

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

lemma degreeUnionBranch62_417_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 26 6 degreeUnionState62_417 [6,8,8,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_417_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_417_oai
