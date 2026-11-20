-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_679
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:38:24.779446+00:00
-- url     : https://prove2.me/submissions/d3ad9a8d-5031-4dc5-bd70-094311f8e0a6

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

lemma degreeUnionBranch62_679_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 28 11 degreeUnionState62_679 [11,11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_679_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_679_oai
