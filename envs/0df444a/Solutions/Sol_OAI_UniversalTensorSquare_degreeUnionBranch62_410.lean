-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_410
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:52:21.976381+00:00
-- url     : https://prove2.me/submissions/11416013-7390-49f7-8d8b-d085925e9fd1

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

lemma degreeUnionBranch62_410_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 29 4 degreeUnionState62_410 [4,7,8,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_410_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_410_oai
