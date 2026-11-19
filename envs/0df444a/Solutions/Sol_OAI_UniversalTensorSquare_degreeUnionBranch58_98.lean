-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_98
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:56:53.236874+00:00
-- url     : https://prove2.me/submissions/c25f75f7-0ddc-4876-9a1e-8aef57e7cae7

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 58. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_98_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 13 48 10 degreeUnionState58_98 [10] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_98_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_98_oai
