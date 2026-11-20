-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_337
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:08:35.299193+00:00
-- url     : https://prove2.me/submissions/d4aec044-f40f-4770-a826-897c3a32e514

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

lemma degreeUnionBranch62_337_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 34 4 degreeUnionState62_337 [4,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_337_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_337_oai
