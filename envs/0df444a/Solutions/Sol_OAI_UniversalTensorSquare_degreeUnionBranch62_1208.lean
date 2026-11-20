-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1208
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:34:57.866833+00:00
-- url     : https://prove2.me/submissions/d8732233-e80d-4d19-801a-0e679f9810f4

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

lemma degreeUnionBranch62_1208_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 27 11 degreeUnionState62_1208 [11,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1208_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1208_oai
