-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_994
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T14:00:42.667179+00:00
-- url     : https://prove2.me/submissions/315ae2a9-bdf6-4138-9dbb-4d2473428bc0

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

lemma degreeUnionBranch62_994_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 26 3 degreeUnionState62_994 [3,11,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_994_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_994_oai
