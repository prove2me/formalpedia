-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_981
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:49:13.98506+00:00
-- url     : https://prove2.me/submissions/abc8a430-3982-4a26-965e-268281226ab4

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

lemma degreeUnionBranch62_981_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 33 7 degreeUnionState62_981 [7,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_981_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_981_oai
