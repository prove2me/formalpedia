-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1221
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:39:14.493177+00:00
-- url     : https://prove2.me/submissions/30ce1bf1-9c02-4201-aac6-5f02ea1de945

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

lemma degreeUnionBranch62_1221_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 28 9 degreeUnionState62_1221 [9,12,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1221_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1221_oai
