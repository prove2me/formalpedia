-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_324
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:02:46.651715+00:00
-- url     : https://prove2.me/submissions/e4aa80d4-00c1-45da-b6f9-f96852d3127a

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

lemma degreeUnionBranch62_324_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 24 6 degreeUnionState62_324 [6,9,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_324_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_324_oai
