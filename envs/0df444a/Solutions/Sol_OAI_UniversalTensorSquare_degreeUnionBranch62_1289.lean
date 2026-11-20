-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1289
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:03:21.103178+00:00
-- url     : https://prove2.me/submissions/b9cca280-89f6-480d-b682-1d0b2f043e2a

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

lemma degreeUnionBranch62_1289_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 24 5 degreeUnionState62_1289 [5,9,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1289_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1289_oai
