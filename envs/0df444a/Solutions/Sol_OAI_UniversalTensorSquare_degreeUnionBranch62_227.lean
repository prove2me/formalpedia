-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_227
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:06:21.136484+00:00
-- url     : https://prove2.me/submissions/dc9167fd-69b6-4dc8-aa28-91264eeda973

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

lemma degreeUnionBranch62_227_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 24 5 degreeUnionState62_227 [5,10,11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_227_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_227_oai
