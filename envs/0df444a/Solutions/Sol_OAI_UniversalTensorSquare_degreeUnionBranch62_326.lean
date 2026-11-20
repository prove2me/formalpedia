-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_326
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:07:43.499387+00:00
-- url     : https://prove2.me/submissions/1c0c9090-0613-409e-9c6e-010311f10641

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

lemma degreeUnionBranch62_326_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 22 8 degreeUnionState62_326 [8,9,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_326_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_326_oai
