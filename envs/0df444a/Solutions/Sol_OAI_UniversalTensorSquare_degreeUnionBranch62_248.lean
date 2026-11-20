-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_248
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:18:21.318178+00:00
-- url     : https://prove2.me/submissions/82517671-8843-4f12-8d70-c9b0a360f1aa

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

lemma degreeUnionBranch62_248_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 22 8 degreeUnionState62_248 [8,8,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_248_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_248_oai
