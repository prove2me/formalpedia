-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_250
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:18:34.023462+00:00
-- url     : https://prove2.me/submissions/021d3bf8-da01-4478-aded-a572d27fe915

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

lemma degreeUnionBranch62_250_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 25 4 degreeUnionState62_250 [4,9,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_250_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_250_oai
