-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_236
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:10:39.728298+00:00
-- url     : https://prove2.me/submissions/4db0e0b8-c6de-4787-b788-8d740c1ad20b

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

lemma degreeUnionBranch62_236_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 33 5 degreeUnionState62_236 [5,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_236_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_236_oai
