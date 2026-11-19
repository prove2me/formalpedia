-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_94
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:51:31.081756+00:00
-- url     : https://prove2.me/submissions/ace45b8b-da83-463b-80c8-5563bdc6393b

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 58. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_94_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 13 52 6 degreeUnionState58_94 [6] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_94_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_94_oai
