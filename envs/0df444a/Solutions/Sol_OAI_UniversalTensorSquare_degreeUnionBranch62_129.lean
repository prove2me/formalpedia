-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_129
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:03:27.236834+00:00
-- url     : https://prove2.me/submissions/7dc95001-6ff1-4604-ba8b-148f044e710d

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

lemma degreeUnionBranch62_129_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 19 10 degreeUnionState62_129 [10,11,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_129_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_129_oai
