-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_976
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:54:25.521062+00:00
-- url     : https://prove2.me/submissions/a6a4cb15-ca66-42a2-8d8c-b627e25c933a

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

lemma degreeUnionBranch62_976_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 31 10 degreeUnionState62_976 [10,10,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_976_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_976_oai
