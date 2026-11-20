-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_39
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:38:46.133018+00:00
-- url     : https://prove2.me/submissions/58c7c28f-21fe-4f82-bb54-7fc45e149af1

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

lemma degreeUnionBranch62_39_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 42 6 degreeUnionState62_39 [6,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_39_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_39_oai
