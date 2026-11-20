-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_692
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:43:34.98364+00:00
-- url     : https://prove2.me/submissions/279647aa-ff49-4bda-bed0-f16a847e7924

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

lemma degreeUnionBranch62_692_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 25 5 degreeUnionState62_692 [5,8,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_692_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_692_oai
