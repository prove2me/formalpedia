-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_778
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:12:54.428141+00:00
-- url     : https://prove2.me/submissions/310d9a71-41f9-4542-8ba5-dd7724155096

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

lemma degreeUnionBranch62_778_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 33 5 degreeUnionState62_778 [5,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_778_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_778_oai
