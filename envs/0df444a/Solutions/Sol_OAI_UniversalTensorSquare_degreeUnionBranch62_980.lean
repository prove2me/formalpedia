-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_980
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:49:06.7665+00:00
-- url     : https://prove2.me/submissions/20435856-6a57-47da-900f-d96946626b39

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

lemma degreeUnionBranch62_980_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 34 6 degreeUnionState62_980 [6,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_980_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_980_oai
