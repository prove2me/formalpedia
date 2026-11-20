-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_817
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:29:35.866174+00:00
-- url     : https://prove2.me/submissions/f5858962-8e98-4454-aae3-89bfb5e08c9e

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

lemma degreeUnionBranch62_817_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 22 7 degreeUnionState62_817 [7,8,12,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_817_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_817_oai
