-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1267
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:54:59.476259+00:00
-- url     : https://prove2.me/submissions/1ee221b2-b348-4038-ae86-aaceb44e603c

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

lemma degreeUnionBranch62_1267_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 27 3 degreeUnionState62_1267 [3,9,9,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1267_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1267_oai
