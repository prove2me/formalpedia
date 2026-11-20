-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_318
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:58:28.935256+00:00
-- url     : https://prove2.me/submissions/d6a81e3f-a17c-4b23-aa93-6dcacf94b85a

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

lemma degreeUnionBranch62_318_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 25 6 degreeUnionState62_318 [6,8,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_318_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_318_oai
