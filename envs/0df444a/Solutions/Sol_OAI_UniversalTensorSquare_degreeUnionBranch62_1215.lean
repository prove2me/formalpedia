-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1215
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:38:54.268702+00:00
-- url     : https://prove2.me/submissions/492eb239-c962-4f94-9414-ef9ea63f2ce5

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

lemma degreeUnionBranch62_1215_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 26 3 degreeUnionState62_1215 [3,8,12,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1215_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1215_oai
