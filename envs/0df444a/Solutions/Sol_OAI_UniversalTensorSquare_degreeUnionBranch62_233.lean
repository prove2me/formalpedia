-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_233
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:10:26.475561+00:00
-- url     : https://prove2.me/submissions/fd67a0e9-34f7-471a-8cbb-4491242dd52b

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

lemma degreeUnionBranch62_233_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 28 11 degreeUnionState62_233 [11,11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_233_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_233_oai
