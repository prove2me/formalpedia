-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_251
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:38:50.409517+00:00
-- url     : https://prove2.me/submissions/90af827c-427c-4779-855e-afd1febeea75

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_251_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 15 14 degreeUnionState43_251 [14,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_251_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_251_oai
