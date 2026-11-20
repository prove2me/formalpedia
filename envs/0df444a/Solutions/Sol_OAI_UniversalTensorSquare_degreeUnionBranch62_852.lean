-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_852
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:45:39.055116+00:00
-- url     : https://prove2.me/submissions/26868a51-be52-4365-8140-f0a0850b525a

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

lemma degreeUnionBranch62_852_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 25 7 degreeUnionState62_852 [7,8,8,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_852_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_852_oai
