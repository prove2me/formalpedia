-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_357
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:26:48.143174+00:00
-- url     : https://prove2.me/submissions/0372c3b0-ed88-41fb-91d6-415b7736d983

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

lemma degreeUnionBranch62_357_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 20 9 degreeUnionState62_357 [9,9,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_357_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_357_oai
