-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_193
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:48:15.01327+00:00
-- url     : https://prove2.me/submissions/ca07e8f8-d892-4d92-8c5f-a66d84fea192

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

lemma degreeUnionBranch62_193_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 23 8 degreeUnionState62_193 [8,9,10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_193_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_193_oai
