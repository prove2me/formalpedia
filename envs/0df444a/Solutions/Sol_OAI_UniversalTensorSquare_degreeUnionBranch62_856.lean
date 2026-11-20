-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_856
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:56:16.904843+00:00
-- url     : https://prove2.me/submissions/e9c40f7a-c90c-4596-b4ee-247b37da7930

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

lemma degreeUnionBranch62_856_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 34 5 degreeUnionState62_856 [5,9,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_856_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_856_oai
