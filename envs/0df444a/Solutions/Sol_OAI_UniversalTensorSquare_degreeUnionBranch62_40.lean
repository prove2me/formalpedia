-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_40
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:42:52.315899+00:00
-- url     : https://prove2.me/submissions/76fe3c64-c085-4be5-8314-38ce7f09c4cd

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

lemma degreeUnionBranch62_40_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 41 7 degreeUnionState62_40 [7,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_40_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_40_oai
