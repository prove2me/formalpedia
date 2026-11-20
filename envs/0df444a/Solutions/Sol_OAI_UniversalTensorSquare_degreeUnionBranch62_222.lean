-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_222
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:01:23.13418+00:00
-- url     : https://prove2.me/submissions/dedfeea7-8390-4be6-9e7a-1b71006a6866

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

lemma degreeUnionBranch62_222_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 23 7 degreeUnionState62_222 [7,9,11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_222_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_222_oai
