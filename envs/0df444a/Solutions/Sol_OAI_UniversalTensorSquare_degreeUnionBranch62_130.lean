-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_130
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:12:06.564577+00:00
-- url     : https://prove2.me/submissions/dbe04da6-f7f8-41f0-949c-a76f76f66151

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

lemma degreeUnionBranch62_130_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 18 11 degreeUnionState62_130 [11,11,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_130_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_130_oai
