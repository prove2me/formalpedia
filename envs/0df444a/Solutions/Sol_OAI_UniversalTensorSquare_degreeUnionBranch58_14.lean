-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_14
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:46:21.608612+00:00
-- url     : https://prove2.me/submissions/5c60b954-104d-475d-8e86-a2468e54edc2

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

lemma degreeUnionBranch58_14_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 52 6 degreeUnionState58_14 [6] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_14_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_14_oai
