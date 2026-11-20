-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_978
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:54:38.587712+00:00
-- url     : https://prove2.me/submissions/939bd92e-ee99-440f-b27d-763475b0638b

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

lemma degreeUnionBranch62_978_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 36 4 degreeUnionState62_978 [4,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_978_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_978_oai
